// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOnEq
// Imports: Lean.Meta.Basic Lean.Meta.Constructions.SparseCasesOn Lean.Meta.HasNotBit Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Refl
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_infer_type, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_contains___redArg};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Core_instInhabitedCoreM___lam__0___boxed;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkAbsurd, l_Lean_Meta_mkEq};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_realizeConst, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Constructions::SparseCasesOn::{
    initialize_Lean_Meta_Constructions_SparseCasesOn, l_Lean_Meta_getSparseCasesOnInfo___redArg,
    l_Lean_Meta_getSparseCasesOnInfoCore, runtime_initialize_Lean_Meta_Constructions_SparseCasesOn,
};
use crate::r#gen::Lean::Meta::HasNotBit::{
    initialize_Lean_Meta_HasNotBit, l_refutableHasNotBit_x3f,
    runtime_initialize_Lean_Meta_HasNotBit,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::{l_Lean_MVarId_assertExt, l_Lean_MVarId_note};
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_MVarId_cases,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    l_Lean_Meta_FVarSubst_apply, l_Lean_Meta_FVarSubst_get,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_intro1Core;
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Subst::l_Lean_Meta_substEq;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_registerReservedNameAction;
use crate::r#gen::Lean::ResolveName::l_Lean_registerReservedNamePredicate;
pub static l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 58, 32, 110, 111, 116, 32, 114, 101, 102, 117, 116, 97, 98, 108, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1_value: crate::leanh::LeanStringObject<88> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 87, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 103, 101, 116, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 46, 114, 101, 97, 108, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 99, 116, 111, 114, 78, 97, 109, 101, 46, 105, 115, 83, 111, 109, 101, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 104, 121, 112, 115, 46, 115, 105, 122, 101, 32, 61, 32, 49, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 104, 121, 112, 32, 116, 121, 112, 101, 32, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [104, 97, 115, 78, 111, 116, 66, 105, 116, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,6351501397486105973 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7_value) as *mut crate::leanh::LeanObject,13438747611467150932 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 105, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10_value) as *mut crate::leanh::LeanObject,1195860576476797317 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 58, 32, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 115, 112, 97, 114, 115, 101, 32, 99, 97, 115, 101, 115, 79, 110, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getSparseCasesOnEq___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 108, 115, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_getSparseCasesOnEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getSparseCasesOnEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<137> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 137, m_capacity: 137, m_length: 136, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 105, 110, 105, 116, 70, 110, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 113, 46, 49, 50, 49, 51, 50, 57, 51, 55, 50, 48, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 50, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 110, 97, 109, 101, 32, 61, 32, 110, 97, 109, 101, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(
    mut v_msg_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_13305__overap_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1672_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0;
    v___x_13305__overap_1673_ = lean_panic_fn_borrowed(v___f_1672_, v_msg_1666_);
    crate::leanh::lean_inc(v___y_1670_);
    crate::leanh::lean_inc_ref(v___y_1669_);
    crate::leanh::lean_inc(v___y_1668_);
    crate::leanh::lean_inc_ref(v___y_1667_);
    v___x_1674_ = crate::leanh::lean_apply_5(
        v___x_13305__overap_1673_,
        v___y_1667_,
        v___y_1668_,
        v___y_1669_,
        v___y_1670_,
        crate::leanh::lean_box(0),
    );
    return v___x_1674_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___boxed(
    mut v_msg_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1681_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
    crate::leanh::lean_dec(v___y_1679_);
    crate::leanh::lean_dec_ref(v___y_1678_);
    crate::leanh::lean_dec(v___y_1677_);
    crate::leanh::lean_dec_ref(v___y_1676_);
    return v_res_1681_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(
    mut v_mvarId_1682_: *mut crate::leanh::LeanObject,
    mut v_x_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut v_a_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1689_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1682_,
                    v_x_1683_,
                    v___y_1684_,
                    v___y_1685_,
                    v___y_1686_,
                    v___y_1687_,
                );
                if crate::leanh::lean_obj_tag(v___x_1689_) == 0 {
                    v_a_1690_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                    v_isSharedCheck_1697_ = (!crate::leanh::lean_is_exclusive(v___x_1689_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1692_ = v___x_1689_;
                        v_isShared_1693_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1690_);
                        crate::leanh::lean_dec(v___x_1689_);
                        v___x_1692_ = crate::leanh::lean_box(0);
                        v_isShared_1693_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1698_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                    v_isSharedCheck_1705_ = (!crate::leanh::lean_is_exclusive(v___x_1689_)) as u8;
                    if v_isSharedCheck_1705_ == 0 {
                        v___x_1700_ = v___x_1689_;
                        v_isShared_1701_ = v_isSharedCheck_1705_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1698_);
                        crate::leanh::lean_dec(v___x_1689_);
                        v___x_1700_ = crate::leanh::lean_box(0);
                        v_isShared_1701_ = v_isSharedCheck_1705_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1693_ == 0 {
                    v___x_1695_ = v___x_1692_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
                    v___x_1695_ = v_reuseFailAlloc_1696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1695_;
            }
            3 => {
                if v_isShared_1701_ == 0 {
                    v___x_1703_ = v___x_1700_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
                    v___x_1703_ = v_reuseFailAlloc_1704_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg___boxed(
    mut v_mvarId_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_mvarId_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
    crate::leanh::lean_dec(v___y_1711_);
    crate::leanh::lean_dec_ref(v___y_1710_);
    crate::leanh::lean_dec(v___y_1709_);
    crate::leanh::lean_dec_ref(v___y_1708_);
    return v_res_1713_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(
    mut v_00_u03b1_1714_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1715_: *mut crate::leanh::LeanObject,
    mut v_x_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_mvarId_1715_, v_x_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
    return v___x_1722_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___boxed(
    mut v_00_u03b1_1723_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1724_: *mut crate::leanh::LeanObject,
    mut v_x_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(v_00_u03b1_1723_, v_mvarId_1724_, v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
    crate::leanh::lean_dec(v___y_1729_);
    crate::leanh::lean_dec_ref(v___y_1728_);
    crate::leanh::lean_dec(v___y_1727_);
    crate::leanh::lean_dec_ref(v___y_1726_);
    return v_res_1731_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(
    mut v_msg_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = crate::leanh::lean_box(0);
    v___x_1734_ = lean_panic_fn_borrowed(v___x_1733_, v_msg_1732_);
    return v___x_1734_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(
    mut v_e_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_unused_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1738_ = l_Lean_Expr_hasMVar(v_e_1735_);
                if v___x_1738_ == 0 {
                    v___x_1739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v_e_1735_);
                    return v___x_1739_;
                } else {
                    v___x_1740_ = lean_st_ref_get(v___y_1736_);
                    v_mctx_1741_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1741_);
                    crate::leanh::lean_dec(v___x_1740_);
                    v___x_1742_ = l_Lean_instantiateMVarsCore(v_mctx_1741_, v_e_1735_);
                    v_fst_1743_ = crate::leanh::lean_ctor_get(v___x_1742_, 0);
                    crate::leanh::lean_inc(v_fst_1743_);
                    v_snd_1744_ = crate::leanh::lean_ctor_get(v___x_1742_, 1);
                    crate::leanh::lean_inc(v_snd_1744_);
                    crate::leanh::lean_dec_ref(v___x_1742_);
                    v___x_1745_ = lean_st_ref_take(v___y_1736_);
                    v_cache_1746_ = crate::leanh::lean_ctor_get(v___x_1745_, 1);
                    v_zetaDeltaFVarIds_1747_ = crate::leanh::lean_ctor_get(v___x_1745_, 2);
                    v_postponed_1748_ = crate::leanh::lean_ctor_get(v___x_1745_, 3);
                    v_diag_1749_ = crate::leanh::lean_ctor_get(v___x_1745_, 4);
                    v_isSharedCheck_1758_ = (!crate::leanh::lean_is_exclusive(v___x_1745_)) as u8;
                    if v_isSharedCheck_1758_ == 0 {
                        v_unused_1759_ = crate::leanh::lean_ctor_get(v___x_1745_, 0);
                        crate::leanh::lean_dec(v_unused_1759_);
                        v___x_1751_ = v___x_1745_;
                        v_isShared_1752_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1749_);
                        crate::leanh::lean_inc(v_postponed_1748_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1747_);
                        crate::leanh::lean_inc(v_cache_1746_);
                        crate::leanh::lean_dec(v___x_1745_);
                        v___x_1751_ = crate::leanh::lean_box(0);
                        v_isShared_1752_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1751_, 0, v_snd_1744_);
                    v___x_1754_ = v___x_1751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_snd_1744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_cache_1746_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1757_,
                        2,
                        v_zetaDeltaFVarIds_1747_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_postponed_1748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_diag_1749_);
                    v___x_1754_ = v_reuseFailAlloc_1757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1755_ = lean_st_ref_set(v___y_1736_, v___x_1754_);
                v___x_1756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1756_, 0, v_fst_1743_);
                return v___x_1756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg___boxed(
    mut v_e_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(v_e_1760_, v___y_1761_);
    crate::leanh::lean_dec(v___y_1761_);
    return v_res_1763_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(
    mut v_e_1764_: *mut crate::leanh::LeanObject,
    mut v___y_1765_: *mut crate::leanh::LeanObject,
    mut v___y_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(v_e_1764_, v___y_1766_);
    return v___x_1770_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___boxed(
    mut v_e_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
    mut v___y_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(v_e_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
    crate::leanh::lean_dec(v___y_1775_);
    crate::leanh::lean_dec_ref(v___y_1774_);
    crate::leanh::lean_dec(v___y_1773_);
    crate::leanh::lean_dec_ref(v___y_1772_);
    return v_res_1777_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0(
    mut v_k_1778_: *mut crate::leanh::LeanObject,
    mut v_b_1779_: *mut crate::leanh::LeanObject,
    mut v_c_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1784_);
    crate::leanh::lean_inc_ref(v___y_1783_);
    crate::leanh::lean_inc(v___y_1782_);
    crate::leanh::lean_inc_ref(v___y_1781_);
    v___x_1786_ = crate::leanh::lean_apply_7(
        v_k_1778_,
        v_b_1779_,
        v_c_1780_,
        v___y_1781_,
        v___y_1782_,
        v___y_1783_,
        v___y_1784_,
        crate::leanh::lean_box(0),
    );
    return v___x_1786_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0___boxed(
    mut v_k_1787_: *mut crate::leanh::LeanObject,
    mut v_b_1788_: *mut crate::leanh::LeanObject,
    mut v_c_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0(v_k_1787_, v_b_1788_, v_c_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
    crate::leanh::lean_dec(v___y_1793_);
    crate::leanh::lean_dec_ref(v___y_1792_);
    crate::leanh::lean_dec(v___y_1791_);
    crate::leanh::lean_dec_ref(v___y_1790_);
    return v_res_1795_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(
    mut v_type_1796_: *mut crate::leanh::LeanObject,
    mut v_k_1797_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1798_: u8,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1804_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1804_, 0, v_k_1797_);
                v___x_1805_ = 0;
                v___x_1806_ = crate::leanh::lean_box(0);
                v___x_1807_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_1805_,
                        v___x_1806_,
                        v_type_1796_,
                        v___f_1804_,
                        v_cleanupAnnotations_1798_,
                        v___x_1805_,
                        v___y_1799_,
                        v___y_1800_,
                        v___y_1801_,
                        v___y_1802_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1807_) == 0 {
                    v_a_1808_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1815_ = (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1810_ = v___x_1807_;
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1808_);
                        crate::leanh::lean_dec(v___x_1807_);
                        v___x_1810_ = crate::leanh::lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1816_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1823_ = (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1807_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1816_);
                        crate::leanh::lean_dec(v___x_1807_);
                        v___x_1818_ = crate::leanh::lean_box(0);
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1813_;
            }
            3 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___boxed(
    mut v_type_1824_: *mut crate::leanh::LeanObject,
    mut v_k_1825_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1832_: u8 = 0;
    let mut v_res_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1832_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1826_) as u8);
    v_res_1833_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_type_1824_, v_k_1825_, v_cleanupAnnotations_boxed_1832_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
    crate::leanh::lean_dec(v___y_1830_);
    crate::leanh::lean_dec_ref(v___y_1829_);
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    return v_res_1833_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(
    mut v_00_u03b1_1834_: *mut crate::leanh::LeanObject,
    mut v_type_1835_: *mut crate::leanh::LeanObject,
    mut v_k_1836_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1837_: u8,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_type_1835_, v_k_1836_, v_cleanupAnnotations_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
    return v___x_1843_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___boxed(
    mut v_00_u03b1_1844_: *mut crate::leanh::LeanObject,
    mut v_type_1845_: *mut crate::leanh::LeanObject,
    mut v_k_1846_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1853_: u8 = 0;
    let mut v_res_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1853_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1847_) as u8);
    v_res_1854_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(v_00_u03b1_1844_, v_type_1845_, v_k_1846_, v_cleanupAnnotations_boxed_1853_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
    crate::leanh::lean_dec(v___y_1851_);
    crate::leanh::lean_dec_ref(v___y_1850_);
    crate::leanh::lean_dec(v___y_1849_);
    crate::leanh::lean_dec_ref(v___y_1848_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(
    mut v_x_1855_: *mut crate::leanh::LeanObject,
    mut v_x_1856_: *mut crate::leanh::LeanObject,
    mut v_x_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1859_ = crate::leanh::lean_ctor_get(v_x_1855_, 0);
                v_vs_1860_ = crate::leanh::lean_ctor_get(v_x_1855_, 1);
                v_isSharedCheck_1884_ = (!crate::leanh::lean_is_exclusive(v_x_1855_)) as u8;
                if v_isSharedCheck_1884_ == 0 {
                    v___x_1862_ = v_x_1855_;
                    v_isShared_1863_ = v_isSharedCheck_1884_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1860_);
                    crate::leanh::lean_inc(v_ks_1859_);
                    crate::leanh::lean_dec(v_x_1855_);
                    v___x_1862_ = crate::leanh::lean_box(0);
                    v_isShared_1863_ = v_isSharedCheck_1884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1864_ = lean_array_get_size(v_ks_1859_);
                v___x_1865_ = lean_nat_dec_lt(v_x_1856_, v___x_1864_);
                if v___x_1865_ == 0 {
                    crate::leanh::lean_dec(v_x_1856_);
                    v___x_1866_ = lean_array_push(v_ks_1859_, v_x_1857_);
                    v___x_1867_ = lean_array_push(v_vs_1860_, v_x_1858_);
                    if v_isShared_1863_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1862_, 1, v___x_1867_);
                        crate::leanh::lean_ctor_set(v___x_1862_, 0, v___x_1866_);
                        v___x_1869_ = v___x_1862_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1870_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1866_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1867_);
                        v___x_1869_ = v_reuseFailAlloc_1870_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1871_ = lean_array_fget_borrowed(v_ks_1859_, v_x_1856_);
                    v___x_1872_ = l_Lean_instBEqMVarId_beq(v_x_1857_, v_k_x27_1871_);
                    if v___x_1872_ == 0 {
                        if v_isShared_1863_ == 0 {
                            v___x_1874_ = v___x_1862_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1878_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_ks_1859_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_vs_1860_);
                            v___x_1874_ = v_reuseFailAlloc_1878_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1879_ = lean_array_fset(v_ks_1859_, v_x_1856_, v_x_1857_);
                        v___x_1880_ = lean_array_fset(v_vs_1860_, v_x_1856_, v_x_1858_);
                        crate::leanh::lean_dec(v_x_1856_);
                        if v_isShared_1863_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1862_, 1, v___x_1880_);
                            crate::leanh::lean_ctor_set(v___x_1862_, 0, v___x_1879_);
                            v___x_1882_ = v___x_1862_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1883_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1879_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1880_);
                            v___x_1882_ = v_reuseFailAlloc_1883_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1869_;
            }
            3 => {
                v___x_1875_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1876_ = lean_nat_add(v_x_1856_, v___x_1875_);
                crate::leanh::lean_dec(v_x_1856_);
                v_x_1855_ = v___x_1874_;
                v_x_1856_ = v___x_1876_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(
    mut v_n_1885_: *mut crate::leanh::LeanObject,
    mut v_k_1886_: *mut crate::leanh::LeanObject,
    mut v_v_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1889_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(v_n_1885_, v___x_1888_, v_k_1886_, v_v_1887_);
    return v___x_1889_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0()
-> usize {
    let mut v___x_1890_: usize = 0;
    let mut v___x_1891_: usize = 0;
    let mut v___x_1892_: usize = 0;
    v___x_1890_ = 5usize;
    v___x_1891_ = 1usize;
    v___x_1892_ = lean_usize_shift_left(v___x_1891_, v___x_1890_);
    return v___x_1892_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__1()
-> usize {
    let mut v___x_1893_: usize = 0;
    let mut v___x_1894_: usize = 0;
    let mut v___x_1895_: usize = 0;
    v___x_1893_ = 1usize;
    v___x_1894_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0);
    v___x_1895_ = lean_usize_sub(v___x_1894_, v___x_1893_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1896_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1896_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(
    mut v_x_1897_: *mut crate::leanh::LeanObject,
    mut v_x_1898_: usize,
    mut v_x_1899_: usize,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
    mut v_x_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: usize = 0;
    let mut v___x_1904_: usize = 0;
    let mut v___x_1905_: usize = 0;
    let mut v___x_1906_: usize = 0;
    let mut v_j_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v_v_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_node_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: usize = 0;
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut v_unused_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1957_: u8 = 0;
    let mut v_ks_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    let mut v_reuseFailAlloc_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1897_) == 0 {
                    v_es_1902_ = crate::leanh::lean_ctor_get(v_x_1897_, 0);
                    v___x_1903_ = 5usize;
                    v___x_1904_ = 1usize;
                    v___x_1905_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__1);
                    v___x_1906_ = lean_usize_land(v_x_1898_, v___x_1905_);
                    v_j_1907_ = lean_usize_to_nat(v___x_1906_);
                    v___x_1908_ = lean_array_get_size(v_es_1902_);
                    v___x_1909_ = lean_nat_dec_lt(v_j_1907_, v___x_1908_);
                    if v___x_1909_ == 0 {
                        crate::leanh::lean_dec(v_j_1907_);
                        crate::leanh::lean_dec(v_x_1901_);
                        crate::leanh::lean_dec(v_x_1900_);
                        return v_x_1897_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1902_);
                        v_isSharedCheck_1946_ = (!crate::leanh::lean_is_exclusive(v_x_1897_)) as u8;
                        if v_isSharedCheck_1946_ == 0 {
                            v_unused_1947_ = crate::leanh::lean_ctor_get(v_x_1897_, 0);
                            crate::leanh::lean_dec(v_unused_1947_);
                            v___x_1911_ = v_x_1897_;
                            v_isShared_1912_ = v_isSharedCheck_1946_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1897_);
                            v___x_1911_ = crate::leanh::lean_box(0);
                            v_isShared_1912_ = v_isSharedCheck_1946_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1948_ = crate::leanh::lean_ctor_get(v_x_1897_, 0);
                    v_vs_1949_ = crate::leanh::lean_ctor_get(v_x_1897_, 1);
                    v_isSharedCheck_1969_ = (!crate::leanh::lean_is_exclusive(v_x_1897_)) as u8;
                    if v_isSharedCheck_1969_ == 0 {
                        v___x_1951_ = v_x_1897_;
                        v_isShared_1952_ = v_isSharedCheck_1969_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1949_);
                        crate::leanh::lean_inc(v_ks_1948_);
                        crate::leanh::lean_dec(v_x_1897_);
                        v___x_1951_ = crate::leanh::lean_box(0);
                        v_isShared_1952_ = v_isSharedCheck_1969_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1913_ = lean_array_fget(v_es_1902_, v_j_1907_);
                v___x_1914_ = crate::leanh::lean_box(0);
                v_xs_x27_1915_ = lean_array_fset(v_es_1902_, v_j_1907_, v___x_1914_);
                match crate::leanh::lean_obj_tag(v_v_1913_) {
                    0 => {
                        v_key_1922_ = crate::leanh::lean_ctor_get(v_v_1913_, 0);
                        v_val_1923_ = crate::leanh::lean_ctor_get(v_v_1913_, 1);
                        v_isSharedCheck_1933_ = (!crate::leanh::lean_is_exclusive(v_v_1913_)) as u8;
                        if v_isSharedCheck_1933_ == 0 {
                            v___x_1925_ = v_v_1913_;
                            v_isShared_1926_ = v_isSharedCheck_1933_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1923_);
                            crate::leanh::lean_inc(v_key_1922_);
                            crate::leanh::lean_dec(v_v_1913_);
                            v___x_1925_ = crate::leanh::lean_box(0);
                            v_isShared_1926_ = v_isSharedCheck_1933_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1934_ = crate::leanh::lean_ctor_get(v_v_1913_, 0);
                        v_isSharedCheck_1944_ = (!crate::leanh::lean_is_exclusive(v_v_1913_)) as u8;
                        if v_isSharedCheck_1944_ == 0 {
                            v___x_1936_ = v_v_1913_;
                            v_isShared_1937_ = v_isSharedCheck_1944_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1934_);
                            crate::leanh::lean_dec(v_v_1913_);
                            v___x_1936_ = crate::leanh::lean_box(0);
                            v_isShared_1937_ = v_isSharedCheck_1944_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1945_, 0, v_x_1900_);
                        crate::leanh::lean_ctor_set(v___x_1945_, 1, v_x_1901_);
                        v___y_1917_ = v___x_1945_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1918_ = lean_array_fset(v_xs_x27_1915_, v_j_1907_, v___y_1917_);
                crate::leanh::lean_dec(v_j_1907_);
                if v_isShared_1912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1911_, 0, v___x_1918_);
                    v___x_1920_ = v___x_1911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
                    v___x_1920_ = v_reuseFailAlloc_1921_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1920_;
            }
            4 => {
                v___x_1927_ = l_Lean_instBEqMVarId_beq(v_x_1900_, v_key_1922_);
                if v___x_1927_ == 0 {
                    crate::leanh::lean_del_object(v___x_1925_);
                    v___x_1928_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1922_,
                        v_val_1923_,
                        v_x_1900_,
                        v_x_1901_,
                    );
                    v___x_1929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1929_, 0, v___x_1928_);
                    v___y_1917_ = v___x_1929_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1923_);
                    crate::leanh::lean_dec(v_key_1922_);
                    if v_isShared_1926_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1925_, 1, v_x_1901_);
                        crate::leanh::lean_ctor_set(v___x_1925_, 0, v_x_1900_);
                        v___x_1931_ = v___x_1925_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_x_1900_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_x_1901_);
                        v___x_1931_ = v_reuseFailAlloc_1932_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1917_ = v___x_1931_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1938_ = lean_usize_shift_right(v_x_1898_, v___x_1903_);
                v___x_1939_ = lean_usize_add(v_x_1899_, v___x_1904_);
                v___x_1940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_node_1934_, v___x_1938_, v___x_1939_, v_x_1900_, v_x_1901_);
                if v_isShared_1937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1940_);
                    v___x_1942_ = v___x_1936_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
                    v___x_1942_ = v_reuseFailAlloc_1943_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1917_ = v___x_1942_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1952_ == 0 {
                    v___x_1954_ = v___x_1951_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1968_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_ks_1948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_vs_1949_);
                    v___x_1954_ = v_reuseFailAlloc_1968_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1955_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(v___x_1954_, v_x_1900_, v_x_1901_);
                v___x_1963_ = 7usize;
                v___x_1964_ = lean_usize_dec_le(v___x_1963_, v_x_1899_);
                if v___x_1964_ == 0 {
                    v___x_1965_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1955_);
                    v___x_1966_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1967_ = lean_nat_dec_lt(v___x_1965_, v___x_1966_);
                    crate::leanh::lean_dec(v___x_1965_);
                    v___y_1957_ = v___x_1967_;
                    state = 10;
                    continue;
                } else {
                    v___y_1957_ = v___x_1964_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1957_ == 0 {
                    v_ks_1958_ = crate::leanh::lean_ctor_get(v_newNode_1955_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1958_);
                    v_vs_1959_ = crate::leanh::lean_ctor_get(v_newNode_1955_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1959_);
                    crate::leanh::lean_dec_ref(v_newNode_1955_);
                    v___x_1960_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1961_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__2);
                    v___x_1962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_x_1899_, v_ks_1958_, v_vs_1959_, v___x_1960_, v___x_1961_);
                    crate::leanh::lean_dec_ref(v_vs_1959_);
                    crate::leanh::lean_dec_ref(v_ks_1958_);
                    return v___x_1962_;
                } else {
                    return v_newNode_1955_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(
    mut v_depth_1970_: usize,
    mut v_keys_1971_: *mut crate::leanh::LeanObject,
    mut v_vals_1972_: *mut crate::leanh::LeanObject,
    mut v_i_1973_: *mut crate::leanh::LeanObject,
    mut v_entries_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v_k_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u64 = 0;
    let mut v_h_1980_: usize = 0;
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: usize = 0;
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: usize = 0;
    let mut v_h_1986_: usize = 0;
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1975_ = lean_array_get_size(v_keys_1971_);
                v___x_1976_ = lean_nat_dec_lt(v_i_1973_, v___x_1975_);
                if v___x_1976_ == 0 {
                    crate::leanh::lean_dec(v_i_1973_);
                    return v_entries_1974_;
                } else {
                    v_k_1977_ = lean_array_fget_borrowed(v_keys_1971_, v_i_1973_);
                    v_v_1978_ = lean_array_fget_borrowed(v_vals_1972_, v_i_1973_);
                    v___x_1979_ = l_Lean_instHashableMVarId_hash(v_k_1977_);
                    v_h_1980_ = lean_uint64_to_usize(v___x_1979_);
                    v___x_1981_ = 5usize;
                    v___x_1982_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1983_ = 1usize;
                    v___x_1984_ = lean_usize_sub(v_depth_1970_, v___x_1983_);
                    v___x_1985_ = lean_usize_mul(v___x_1981_, v___x_1984_);
                    v_h_1986_ = lean_usize_shift_right(v_h_1980_, v___x_1985_);
                    v___x_1987_ = lean_nat_add(v_i_1973_, v___x_1982_);
                    crate::leanh::lean_dec(v_i_1973_);
                    crate::leanh::lean_inc(v_v_1978_);
                    crate::leanh::lean_inc(v_k_1977_);
                    v___x_1988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_entries_1974_, v_h_1986_, v_depth_1970_, v_k_1977_, v_v_1978_);
                    v_i_1973_ = v___x_1987_;
                    v_entries_1974_ = v___x_1988_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg___boxed(
    mut v_depth_1990_: *mut crate::leanh::LeanObject,
    mut v_keys_1991_: *mut crate::leanh::LeanObject,
    mut v_vals_1992_: *mut crate::leanh::LeanObject,
    mut v_i_1993_: *mut crate::leanh::LeanObject,
    mut v_entries_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1995_: usize = 0;
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1995_ = crate::leanh::lean_unbox_usize(v_depth_1990_);
    crate::leanh::lean_dec(v_depth_1990_);
    v_res_1996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_depth_boxed_1995_, v_keys_1991_, v_vals_1992_, v_i_1993_, v_entries_1994_);
    crate::leanh::lean_dec_ref(v_vals_1992_);
    crate::leanh::lean_dec_ref(v_keys_1991_);
    return v_res_1996_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___boxed(
    mut v_x_1997_: *mut crate::leanh::LeanObject,
    mut v_x_1998_: *mut crate::leanh::LeanObject,
    mut v_x_1999_: *mut crate::leanh::LeanObject,
    mut v_x_2000_: *mut crate::leanh::LeanObject,
    mut v_x_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18880__boxed_2002_: usize = 0;
    let mut v_x_18881__boxed_2003_: usize = 0;
    let mut v_res_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18880__boxed_2002_ = crate::leanh::lean_unbox_usize(v_x_1998_);
    crate::leanh::lean_dec(v_x_1998_);
    v_x_18881__boxed_2003_ = crate::leanh::lean_unbox_usize(v_x_1999_);
    crate::leanh::lean_dec(v_x_1999_);
    v_res_2004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_1997_, v_x_18880__boxed_2002_, v_x_18881__boxed_2003_, v_x_2000_, v_x_2001_);
    return v_res_2004_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(
    mut v_x_2005_: *mut crate::leanh::LeanObject,
    mut v_x_2006_: *mut crate::leanh::LeanObject,
    mut v_x_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2008_: u64 = 0;
    let mut v___x_2009_: usize = 0;
    let mut v___x_2010_: usize = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ = l_Lean_instHashableMVarId_hash(v_x_2006_);
    v___x_2009_ = lean_uint64_to_usize(v___x_2008_);
    v___x_2010_ = 1usize;
    v___x_2011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_2005_, v___x_2009_, v___x_2010_, v_x_2006_, v_x_2007_);
    return v___x_2011_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(
    mut v_mvarId_2012_: *mut crate::leanh::LeanObject,
    mut v_val_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v_depth_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2048_: u8 = 0;
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2016_ = lean_st_ref_take(v___y_2014_);
                v_mctx_2017_ = crate::leanh::lean_ctor_get(v___x_2016_, 0);
                v_cache_2018_ = crate::leanh::lean_ctor_get(v___x_2016_, 1);
                v_zetaDeltaFVarIds_2019_ = crate::leanh::lean_ctor_get(v___x_2016_, 2);
                v_postponed_2020_ = crate::leanh::lean_ctor_get(v___x_2016_, 3);
                v_diag_2021_ = crate::leanh::lean_ctor_get(v___x_2016_, 4);
                v_isSharedCheck_2049_ = (!crate::leanh::lean_is_exclusive(v___x_2016_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v___x_2023_ = v___x_2016_;
                    v_isShared_2024_ = v_isSharedCheck_2049_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2021_);
                    crate::leanh::lean_inc(v_postponed_2020_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2019_);
                    crate::leanh::lean_inc(v_cache_2018_);
                    crate::leanh::lean_inc(v_mctx_2017_);
                    crate::leanh::lean_dec(v___x_2016_);
                    v___x_2023_ = crate::leanh::lean_box(0);
                    v_isShared_2024_ = v_isSharedCheck_2049_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2025_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 0);
                v_levelAssignDepth_2026_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 1);
                v_lmvarCounter_2027_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 2);
                v_mvarCounter_2028_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 3);
                v_lDecls_2029_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 4);
                v_decls_2030_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 5);
                v_userNames_2031_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 6);
                v_lAssignment_2032_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 7);
                v_eAssignment_2033_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 8);
                v_dAssignment_2034_ = crate::leanh::lean_ctor_get(v_mctx_2017_, 9);
                v_isSharedCheck_2048_ = (!crate::leanh::lean_is_exclusive(v_mctx_2017_)) as u8;
                if v_isSharedCheck_2048_ == 0 {
                    v___x_2036_ = v_mctx_2017_;
                    v_isShared_2037_ = v_isSharedCheck_2048_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2034_);
                    crate::leanh::lean_inc(v_eAssignment_2033_);
                    crate::leanh::lean_inc(v_lAssignment_2032_);
                    crate::leanh::lean_inc(v_userNames_2031_);
                    crate::leanh::lean_inc(v_decls_2030_);
                    crate::leanh::lean_inc(v_lDecls_2029_);
                    crate::leanh::lean_inc(v_mvarCounter_2028_);
                    crate::leanh::lean_inc(v_lmvarCounter_2027_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2026_);
                    crate::leanh::lean_inc(v_depth_2025_);
                    crate::leanh::lean_dec(v_mctx_2017_);
                    v___x_2036_ = crate::leanh::lean_box(0);
                    v_isShared_2037_ = v_isSharedCheck_2048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2038_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(v_eAssignment_2033_, v_mvarId_2012_, v_val_2013_);
                if v_isShared_2037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2036_, 8, v___x_2038_);
                    v___x_2040_ = v___x_2036_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2047_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_depth_2025_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2047_,
                        1,
                        v_levelAssignDepth_2026_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_lmvarCounter_2027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_mvarCounter_2028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_lDecls_2029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 5, v_decls_2030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 6, v_userNames_2031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 7, v_lAssignment_2032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 8, v___x_2038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 9, v_dAssignment_2034_);
                    v___x_2040_ = v_reuseFailAlloc_2047_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2040_);
                    v___x_2042_ = v___x_2023_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_cache_2018_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2046_,
                        2,
                        v_zetaDeltaFVarIds_2019_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_postponed_2020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 4, v_diag_2021_);
                    v___x_2042_ = v_reuseFailAlloc_2046_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2043_ = lean_st_ref_set(v___y_2014_, v___x_2042_);
                v___x_2044_ = crate::leanh::lean_box(0);
                v___x_2045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2045_, 0, v___x_2044_);
                return v___x_2045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg___boxed(
    mut v_mvarId_2050_: *mut crate::leanh::LeanObject,
    mut v_val_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_mvarId_2050_, v_val_2051_, v___y_2052_);
    crate::leanh::lean_dec(v___y_2052_);
    return v_res_2054_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(
    mut v_msgData_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2061_ = lean_st_ref_get(v___y_2059_);
    v_env_2062_ = crate::leanh::lean_ctor_get(v___x_2061_, 0);
    crate::leanh::lean_inc_ref(v_env_2062_);
    crate::leanh::lean_dec(v___x_2061_);
    v___x_2063_ = lean_st_ref_get(v___y_2057_);
    v_mctx_2064_ = crate::leanh::lean_ctor_get(v___x_2063_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2064_);
    crate::leanh::lean_dec(v___x_2063_);
    v_lctx_2065_ = crate::leanh::lean_ctor_get(v___y_2056_, 2);
    v_options_2066_ = crate::leanh::lean_ctor_get(v___y_2058_, 2);
    crate::leanh::lean_inc_ref(v_options_2066_);
    crate::leanh::lean_inc_ref(v_lctx_2065_);
    v___x_2067_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2067_, 0, v_env_2062_);
    crate::leanh::lean_ctor_set(v___x_2067_, 1, v_mctx_2064_);
    crate::leanh::lean_ctor_set(v___x_2067_, 2, v_lctx_2065_);
    crate::leanh::lean_ctor_set(v___x_2067_, 3, v_options_2066_);
    v___x_2068_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2068_, 0, v___x_2067_);
    crate::leanh::lean_ctor_set(v___x_2068_, 1, v_msgData_2055_);
    v___x_2069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2068_);
    return v___x_2069_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4___boxed(
    mut v_msgData_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
    mut v___y_2074_: *mut crate::leanh::LeanObject,
    mut v___y_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(v_msgData_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
    crate::leanh::lean_dec(v___y_2074_);
    crate::leanh::lean_dec_ref(v___y_2073_);
    crate::leanh::lean_dec(v___y_2072_);
    crate::leanh::lean_dec_ref(v___y_2071_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(
    mut v_msg_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2088_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2083_ = crate::leanh::lean_ctor_get(v___y_2080_, 5);
                v___x_2084_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(v_msg_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
                v_a_2085_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                v_isSharedCheck_2093_ = (!crate::leanh::lean_is_exclusive(v___x_2084_)) as u8;
                if v_isSharedCheck_2093_ == 0 {
                    v___x_2087_ = v___x_2084_;
                    v_isShared_2088_ = v_isSharedCheck_2093_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2085_);
                    crate::leanh::lean_dec(v___x_2084_);
                    v___x_2087_ = crate::leanh::lean_box(0);
                    v_isShared_2088_ = v_isSharedCheck_2093_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2083_);
                v___x_2089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2089_, 0, v_ref_2083_);
                crate::leanh::lean_ctor_set(v___x_2089_, 1, v_a_2085_);
                if v_isShared_2088_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2087_, 1);
                    crate::leanh::lean_ctor_set(v___x_2087_, 0, v___x_2089_);
                    v___x_2091_ = v___x_2087_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
                    v___x_2091_ = v_reuseFailAlloc_2092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg___boxed(
    mut v_msg_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
    crate::leanh::lean_dec(v___y_2098_);
    crate::leanh::lean_dec_ref(v___y_2097_);
    crate::leanh::lean_dec(v___y_2096_);
    crate::leanh::lean_dec_ref(v___y_2095_);
    return v_res_2100_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0;
    v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
    return v___x_2103_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0(
    mut v___x_2104_: *mut crate::leanh::LeanObject,
    mut v_snd_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
    mut v___y_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_a_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2132_: u8 = 0;
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_a_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_a_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2109_);
                crate::leanh::lean_inc_ref(v___y_2108_);
                crate::leanh::lean_inc(v___y_2107_);
                crate::leanh::lean_inc_ref(v___y_2106_);
                crate::leanh::lean_inc_ref(v___x_2104_);
                v___x_2111_ = lean_infer_type(
                    v___x_2104_,
                    v___y_2106_,
                    v___y_2107_,
                    v___y_2108_,
                    v___y_2109_,
                );
                if crate::leanh::lean_obj_tag(v___x_2111_) == 0 {
                    v_a_2112_ = crate::leanh::lean_ctor_get(v___x_2111_, 0);
                    crate::leanh::lean_inc(v_a_2112_);
                    crate::leanh::lean_dec_ref_known(v___x_2111_, 1);
                    v___x_2113_ = l_refutableHasNotBit_x3f(
                        v_a_2112_,
                        v___y_2106_,
                        v___y_2107_,
                        v___y_2108_,
                        v___y_2109_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2113_) == 0 {
                        v_a_2114_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        crate::leanh::lean_inc(v_a_2114_);
                        crate::leanh::lean_dec_ref_known(v___x_2113_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2114_) == 1 {
                            v_val_2115_ = crate::leanh::lean_ctor_get(v_a_2114_, 0);
                            crate::leanh::lean_inc(v_val_2115_);
                            crate::leanh::lean_dec_ref_known(v_a_2114_, 1);
                            crate::leanh::lean_inc(v_snd_2105_);
                            v___x_2116_ = l_Lean_MVarId_getType(
                                v_snd_2105_,
                                v___y_2106_,
                                v___y_2107_,
                                v___y_2108_,
                                v___y_2109_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2116_) == 0 {
                                v_a_2117_ = crate::leanh::lean_ctor_get(v___x_2116_, 0);
                                crate::leanh::lean_inc(v_a_2117_);
                                crate::leanh::lean_dec_ref_known(v___x_2116_, 1);
                                v___x_2118_ = l_Lean_Meta_mkAbsurd(
                                    v_a_2117_,
                                    v_val_2115_,
                                    v___x_2104_,
                                    v___y_2106_,
                                    v___y_2107_,
                                    v___y_2108_,
                                    v___y_2109_,
                                );
                                crate::leanh::lean_dec(v___y_2109_);
                                crate::leanh::lean_dec_ref(v___y_2108_);
                                crate::leanh::lean_dec_ref(v___y_2106_);
                                if crate::leanh::lean_obj_tag(v___x_2118_) == 0 {
                                    v_a_2119_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                                    crate::leanh::lean_inc(v_a_2119_);
                                    crate::leanh::lean_dec_ref_known(v___x_2118_, 1);
                                    v___x_2120_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_snd_2105_, v_a_2119_, v___y_2107_);
                                    crate::leanh::lean_dec(v___y_2107_);
                                    return v___x_2120_;
                                } else {
                                    crate::leanh::lean_dec(v___y_2107_);
                                    crate::leanh::lean_dec(v_snd_2105_);
                                    v_a_2121_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                                    v_isSharedCheck_2128_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2118_)) as u8;
                                    if v_isSharedCheck_2128_ == 0 {
                                        v___x_2123_ = v___x_2118_;
                                        v_isShared_2124_ = v_isSharedCheck_2128_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2121_);
                                        crate::leanh::lean_dec(v___x_2118_);
                                        v___x_2123_ = crate::leanh::lean_box(0);
                                        v_isShared_2124_ = v_isSharedCheck_2128_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_2115_);
                                crate::leanh::lean_dec(v___y_2109_);
                                crate::leanh::lean_dec_ref(v___y_2108_);
                                crate::leanh::lean_dec(v___y_2107_);
                                crate::leanh::lean_dec_ref(v___y_2106_);
                                crate::leanh::lean_dec(v_snd_2105_);
                                crate::leanh::lean_dec_ref(v___x_2104_);
                                v_a_2129_ = crate::leanh::lean_ctor_get(v___x_2116_, 0);
                                v_isSharedCheck_2136_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2116_)) as u8;
                                if v_isSharedCheck_2136_ == 0 {
                                    v___x_2131_ = v___x_2116_;
                                    v_isShared_2132_ = v_isSharedCheck_2136_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2129_);
                                    crate::leanh::lean_dec(v___x_2116_);
                                    v___x_2131_ = crate::leanh::lean_box(0);
                                    v_isShared_2132_ = v_isSharedCheck_2136_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2114_);
                            crate::leanh::lean_dec(v_snd_2105_);
                            crate::leanh::lean_inc(v___y_2109_);
                            crate::leanh::lean_inc_ref(v___y_2108_);
                            crate::leanh::lean_inc(v___y_2107_);
                            crate::leanh::lean_inc_ref(v___y_2106_);
                            v___x_2137_ = lean_infer_type(
                                v___x_2104_,
                                v___y_2106_,
                                v___y_2107_,
                                v___y_2108_,
                                v___y_2109_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2137_) == 0 {
                                v_a_2138_ = crate::leanh::lean_ctor_get(v___x_2137_, 0);
                                crate::leanh::lean_inc(v_a_2138_);
                                crate::leanh::lean_dec_ref_known(v___x_2137_, 1);
                                v___x_2139_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1);
                                v___x_2140_ = l_Lean_MessageData_ofExpr(v_a_2138_);
                                v___x_2141_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2139_);
                                crate::leanh::lean_ctor_set(v___x_2141_, 1, v___x_2140_);
                                v___x_2142_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_2141_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
                                crate::leanh::lean_dec(v___y_2109_);
                                crate::leanh::lean_dec_ref(v___y_2108_);
                                crate::leanh::lean_dec(v___y_2107_);
                                crate::leanh::lean_dec_ref(v___y_2106_);
                                return v___x_2142_;
                            } else {
                                crate::leanh::lean_dec(v___y_2109_);
                                crate::leanh::lean_dec_ref(v___y_2108_);
                                crate::leanh::lean_dec(v___y_2107_);
                                crate::leanh::lean_dec_ref(v___y_2106_);
                                v_a_2143_ = crate::leanh::lean_ctor_get(v___x_2137_, 0);
                                v_isSharedCheck_2150_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2137_)) as u8;
                                if v_isSharedCheck_2150_ == 0 {
                                    v___x_2145_ = v___x_2137_;
                                    v_isShared_2146_ = v_isSharedCheck_2150_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2143_);
                                    crate::leanh::lean_dec(v___x_2137_);
                                    v___x_2145_ = crate::leanh::lean_box(0);
                                    v_isShared_2146_ = v_isSharedCheck_2150_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2109_);
                        crate::leanh::lean_dec_ref(v___y_2108_);
                        crate::leanh::lean_dec(v___y_2107_);
                        crate::leanh::lean_dec_ref(v___y_2106_);
                        crate::leanh::lean_dec(v_snd_2105_);
                        crate::leanh::lean_dec_ref(v___x_2104_);
                        v_a_2151_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        v_isSharedCheck_2158_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2158_ == 0 {
                            v___x_2153_ = v___x_2113_;
                            v_isShared_2154_ = v_isSharedCheck_2158_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2151_);
                            crate::leanh::lean_dec(v___x_2113_);
                            v___x_2153_ = crate::leanh::lean_box(0);
                            v_isShared_2154_ = v_isSharedCheck_2158_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2109_);
                    crate::leanh::lean_dec_ref(v___y_2108_);
                    crate::leanh::lean_dec(v___y_2107_);
                    crate::leanh::lean_dec_ref(v___y_2106_);
                    crate::leanh::lean_dec(v_snd_2105_);
                    crate::leanh::lean_dec_ref(v___x_2104_);
                    v_a_2159_ = crate::leanh::lean_ctor_get(v___x_2111_, 0);
                    v_isSharedCheck_2166_ = (!crate::leanh::lean_is_exclusive(v___x_2111_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v___x_2161_ = v___x_2111_;
                        v_isShared_2162_ = v_isSharedCheck_2166_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2159_);
                        crate::leanh::lean_dec(v___x_2111_);
                        v___x_2161_ = crate::leanh::lean_box(0);
                        v_isShared_2162_ = v_isSharedCheck_2166_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2124_ == 0 {
                    v___x_2126_ = v___x_2123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
                    v___x_2126_ = v_reuseFailAlloc_2127_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2126_;
            }
            3 => {
                if v_isShared_2132_ == 0 {
                    v___x_2134_ = v___x_2131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
                    v___x_2134_ = v_reuseFailAlloc_2135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2134_;
            }
            5 => {
                if v_isShared_2146_ == 0 {
                    v___x_2148_ = v___x_2145_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2148_;
            }
            7 => {
                if v_isShared_2154_ == 0 {
                    v___x_2156_ = v___x_2153_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2157_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2156_;
            }
            9 => {
                if v_isShared_2162_ == 0 {
                    v___x_2164_ = v___x_2161_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
                    v___x_2164_ = v_reuseFailAlloc_2165_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___boxed(
    mut v___x_2167_: *mut crate::leanh::LeanObject,
    mut v_snd_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0(v___x_2167_, v_snd_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
    return v_res_2174_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2;
    v___x_2179_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_2180_ = crate::leanh::lean_unsigned_to_nat(63);
    v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1;
    v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0;
    v___x_2183_ = l_mkPanicMessageWithDecl(
        v___x_2182_,
        v___x_2181_,
        v___x_2180_,
        v___x_2179_,
        v___x_2178_,
    );
    return v___x_2183_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7;
    v___x_2189_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2190_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6;
    v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5;
    v___x_2193_ = l_mkPanicMessageWithDecl(
        v___x_2192_,
        v___x_2191_,
        v___x_2190_,
        v___x_2189_,
        v___x_2188_,
    );
    return v___x_2193_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1(
    mut v___y_2194_: u8,
    mut v_val_2195_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2196_: *mut crate::leanh::LeanObject,
    mut v___x_2197_: u8,
    mut v_subst_2198_: *mut crate::leanh::LeanObject,
    mut v_fst_2199_: *mut crate::leanh::LeanObject,
    mut v___x_2200_: *mut crate::leanh::LeanObject,
    mut v_fst_2201_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insterestingCtors_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: u8 = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2194_ == 0 {
                    crate::leanh::lean_dec(v_ctorName_2202_);
                    crate::leanh::lean_dec(v_fst_2201_);
                    crate::leanh::lean_dec(v___x_2200_);
                    crate::leanh::lean_dec(v_fst_2199_);
                    crate::leanh::lean_dec(v_mvarId_2196_);
                    crate::leanh::lean_dec_ref(v_val_2195_);
                    v___x_2208_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3);
                    v___x_2209_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v___x_2208_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
                    return v___x_2209_;
                } else {
                    v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4;
                    if crate::leanh::lean_obj_tag(v_ctorName_2202_) == 0 {
                        v___x_2234_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8);
                        v___x_2235_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(v___x_2234_);
                        v___y_2212_ = v___x_2235_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2236_ = crate::leanh::lean_ctor_get(v_ctorName_2202_, 0);
                        crate::leanh::lean_inc(v_val_2236_);
                        crate::leanh::lean_dec_ref_known(v_ctorName_2202_, 1);
                        v___y_2212_ = v_val_2236_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_insterestingCtors_2213_ = crate::leanh::lean_ctor_get(v_val_2195_, 3);
                crate::leanh::lean_inc_ref(v_insterestingCtors_2213_);
                crate::leanh::lean_dec_ref(v_val_2195_);
                v___x_2214_ =
                    l_Array_contains___redArg(v___x_2210_, v_insterestingCtors_2213_, v___y_2212_);
                if v___x_2214_ == 0 {
                    crate::leanh::lean_dec(v_fst_2201_);
                    crate::leanh::lean_dec(v___x_2200_);
                    crate::leanh::lean_dec(v_fst_2199_);
                    v___x_2215_ = l_Lean_MVarId_refl(
                        v_mvarId_2196_,
                        v___x_2197_,
                        v___y_2203_,
                        v___y_2204_,
                        v___y_2205_,
                        v___y_2206_,
                    );
                    return v___x_2215_;
                } else {
                    v___x_2216_ = l_Lean_Meta_FVarSubst_get(v_subst_2198_, v_fst_2199_);
                    v___x_2217_ = l_Lean_Expr_fvarId_x21(v___x_2216_);
                    crate::leanh::lean_dec_ref(v___x_2216_);
                    v___x_2218_ = l_Lean_Meta_substEq(
                        v_mvarId_2196_,
                        v___x_2217_,
                        v___x_2200_,
                        v___y_2203_,
                        v___y_2204_,
                        v___y_2205_,
                        v___y_2206_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2218_) == 0 {
                        v_a_2219_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                        crate::leanh::lean_inc(v_a_2219_);
                        crate::leanh::lean_dec_ref_known(v___x_2218_, 1);
                        v_fst_2220_ = crate::leanh::lean_ctor_get(v_a_2219_, 0);
                        crate::leanh::lean_inc(v_fst_2220_);
                        v_snd_2221_ = crate::leanh::lean_ctor_get(v_a_2219_, 1);
                        crate::leanh::lean_inc_n(v_snd_2221_, 2);
                        crate::leanh::lean_dec(v_a_2219_);
                        v___x_2222_ = l_Lean_Meta_FVarSubst_get(v_subst_2198_, v_fst_2201_);
                        v___x_2223_ = l_Lean_Meta_FVarSubst_apply(v_fst_2220_, v___x_2222_);
                        crate::leanh::lean_dec_ref(v___x_2222_);
                        v___f_2224_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                        crate::leanh::lean_closure_set(v___f_2224_, 0, v___x_2223_);
                        crate::leanh::lean_closure_set(v___f_2224_, 1, v_snd_2221_);
                        v___x_2225_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_snd_2221_, v___f_2224_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
                        return v___x_2225_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2201_);
                        v_a_2226_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                        v_isSharedCheck_2233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                        if v_isSharedCheck_2233_ == 0 {
                            v___x_2228_ = v___x_2218_;
                            v_isShared_2229_ = v_isSharedCheck_2233_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2226_);
                            crate::leanh::lean_dec(v___x_2218_);
                            v___x_2228_ = crate::leanh::lean_box(0);
                            v_isShared_2229_ = v_isSharedCheck_2233_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2229_ == 0 {
                    v___x_2231_ = v___x_2228_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___boxed(
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v_val_2238_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2239_: *mut crate::leanh::LeanObject,
    mut v___x_2240_: *mut crate::leanh::LeanObject,
    mut v_subst_2241_: *mut crate::leanh::LeanObject,
    mut v_fst_2242_: *mut crate::leanh::LeanObject,
    mut v___x_2243_: *mut crate::leanh::LeanObject,
    mut v_fst_2244_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_19340__boxed_2251_: u8 = 0;
    let mut v___x_19342__boxed_2252_: u8 = 0;
    let mut v_res_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_19340__boxed_2251_ = (crate::leanh::lean_unbox(v___y_2237_) as u8);
    v___x_19342__boxed_2252_ = (crate::leanh::lean_unbox(v___x_2240_) as u8);
    v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1(v___y_19340__boxed_2251_, v_val_2238_, v_mvarId_2239_, v___x_19342__boxed_2252_, v_subst_2241_, v_fst_2242_, v___x_2243_, v_fst_2244_, v_ctorName_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
    crate::leanh::lean_dec(v___y_2249_);
    crate::leanh::lean_dec_ref(v___y_2248_);
    crate::leanh::lean_dec(v___y_2247_);
    crate::leanh::lean_dec_ref(v___y_2246_);
    crate::leanh::lean_dec(v_subst_2241_);
    return v_res_2253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(
    mut v_val_2254_: *mut crate::leanh::LeanObject,
    mut v___x_2255_: u8,
    mut v_fst_2256_: *mut crate::leanh::LeanObject,
    mut v_fst_2257_: *mut crate::leanh::LeanObject,
    mut v_as_2258_: *mut crate::leanh::LeanObject,
    mut v_i_2259_: usize,
    mut v_stop_2260_: usize,
    mut v_b_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2267_ = lean_usize_dec_eq(v_i_2259_, v_stop_2260_);
                if v___x_2267_ == 0 {
                    v___x_2268_ = lean_array_uget_borrowed(v_as_2258_, v_i_2259_);
                    v_toInductionSubgoal_2269_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                    v_ctorName_2270_ = crate::leanh::lean_ctor_get(v___x_2268_, 1);
                    v_mvarId_2271_ = crate::leanh::lean_ctor_get(v_toInductionSubgoal_2269_, 0);
                    v_subst_2272_ = crate::leanh::lean_ctor_get(v_toInductionSubgoal_2269_, 2);
                    v___x_2273_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_ctorName_2270_) == 0 {
                        v___y_2275_ = v___x_2267_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_2255_ == 0 {
                            v___y_2275_ = v___x_2267_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2275_ = v___x_2255_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2257_);
                    crate::leanh::lean_dec(v_fst_2256_);
                    crate::leanh::lean_dec_ref(v_val_2254_);
                    v___x_2284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2284_, 0, v_b_2261_);
                    return v___x_2284_;
                }
            }
            1 => {
                v___x_2276_ = crate::leanh::lean_box((v___y_2275_) as usize);
                v___x_2277_ = crate::leanh::lean_box((v___x_2255_) as usize);
                crate::leanh::lean_inc(v_ctorName_2270_);
                crate::leanh::lean_inc(v_fst_2257_);
                crate::leanh::lean_inc(v_fst_2256_);
                crate::leanh::lean_inc(v_subst_2272_);
                crate::leanh::lean_inc_n(v_mvarId_2271_, 2);
                crate::leanh::lean_inc_ref(v_val_2254_);
                v___y_2278_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___boxed as *mut core::ffi::c_void, 14, 9);
                crate::leanh::lean_closure_set(v___y_2278_, 0, v___x_2276_);
                crate::leanh::lean_closure_set(v___y_2278_, 1, v_val_2254_);
                crate::leanh::lean_closure_set(v___y_2278_, 2, v_mvarId_2271_);
                crate::leanh::lean_closure_set(v___y_2278_, 3, v___x_2277_);
                crate::leanh::lean_closure_set(v___y_2278_, 4, v_subst_2272_);
                crate::leanh::lean_closure_set(v___y_2278_, 5, v_fst_2256_);
                crate::leanh::lean_closure_set(v___y_2278_, 6, v___x_2273_);
                crate::leanh::lean_closure_set(v___y_2278_, 7, v_fst_2257_);
                crate::leanh::lean_closure_set(v___y_2278_, 8, v_ctorName_2270_);
                v___x_2279_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_mvarId_2271_, v___y_2278_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
                if crate::leanh::lean_obj_tag(v___x_2279_) == 0 {
                    v_a_2280_ = crate::leanh::lean_ctor_get(v___x_2279_, 0);
                    crate::leanh::lean_inc(v_a_2280_);
                    crate::leanh::lean_dec_ref_known(v___x_2279_, 1);
                    v___x_2281_ = 1usize;
                    v___x_2282_ = lean_usize_add(v_i_2259_, v___x_2281_);
                    v_i_2259_ = v___x_2282_;
                    v_b_2261_ = v_a_2280_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2257_);
                    crate::leanh::lean_dec(v_fst_2256_);
                    crate::leanh::lean_dec_ref(v_val_2254_);
                    return v___x_2279_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___boxed(
    mut v_val_2285_: *mut crate::leanh::LeanObject,
    mut v___x_2286_: *mut crate::leanh::LeanObject,
    mut v_fst_2287_: *mut crate::leanh::LeanObject,
    mut v_fst_2288_: *mut crate::leanh::LeanObject,
    mut v_as_2289_: *mut crate::leanh::LeanObject,
    mut v_i_2290_: *mut crate::leanh::LeanObject,
    mut v_stop_2291_: *mut crate::leanh::LeanObject,
    mut v_b_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_19449__boxed_2298_: u8 = 0;
    let mut v_i_boxed_2299_: usize = 0;
    let mut v_stop_boxed_2300_: usize = 0;
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_19449__boxed_2298_ = (crate::leanh::lean_unbox(v___x_2286_) as u8);
    v_i_boxed_2299_ = crate::leanh::lean_unbox_usize(v_i_2290_);
    crate::leanh::lean_dec(v_i_2290_);
    v_stop_boxed_2300_ = crate::leanh::lean_unbox_usize(v_stop_2291_);
    crate::leanh::lean_dec(v_stop_2291_);
    v_res_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_val_2285_, v___x_19449__boxed_2298_, v_fst_2287_, v_fst_2288_, v_as_2289_, v_i_boxed_2299_, v_stop_boxed_2300_, v_b_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
    crate::leanh::lean_dec(v___y_2296_);
    crate::leanh::lean_dec_ref(v___y_2295_);
    crate::leanh::lean_dec(v___y_2294_);
    crate::leanh::lean_dec_ref(v___y_2293_);
    crate::leanh::lean_dec_ref(v_as_2289_);
    return v_res_2301_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(
    mut v___x_2305_: *mut crate::leanh::LeanObject,
    mut v___x_2306_: *mut crate::leanh::LeanObject,
    mut v_fst_2307_: *mut crate::leanh::LeanObject,
    mut v___x_2308_: *mut crate::leanh::LeanObject,
    mut v_snd_2309_: *mut crate::leanh::LeanObject,
    mut v_val_2310_: *mut crate::leanh::LeanObject,
    mut v___x_2311_: *mut crate::leanh::LeanObject,
    mut v_xs_2312_: *mut crate::leanh::LeanObject,
    mut v___x_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v_hyps_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v___x_2317_: u8,
    mut v_thmName_2318_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2347_: u8 = 0;
    let mut v_majorPos_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: u8 = 0;
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_a_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2390_: u8 = 0;
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut v___y_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: usize = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_a_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2423_: u8 = 0;
    let mut v_reuseFailAlloc_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_unused_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut v_a_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___x_2305_);
                v___x_2325_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_2305_,
                    v___x_2306_,
                    v___y_2320_,
                    v___y_2321_,
                    v___y_2322_,
                    v___y_2323_,
                );
                if crate::leanh::lean_obj_tag(v___x_2325_) == 0 {
                    v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2325_, 0);
                    crate::leanh::lean_inc(v_a_2326_);
                    crate::leanh::lean_dec_ref_known(v___x_2325_, 1);
                    v___x_2327_ = l_Lean_Expr_mvarId_x21(v_a_2326_);
                    v___x_2328_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_2307_);
                    v___x_2329_ = l_Lean_Meta_substEq(
                        v___x_2327_,
                        v_fst_2307_,
                        v___x_2328_,
                        v___y_2320_,
                        v___y_2321_,
                        v___y_2322_,
                        v___y_2323_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2329_) == 0 {
                        v_a_2330_ = crate::leanh::lean_ctor_get(v___x_2329_, 0);
                        crate::leanh::lean_inc(v_a_2330_);
                        crate::leanh::lean_dec_ref_known(v___x_2329_, 1);
                        v_fst_2331_ = crate::leanh::lean_ctor_get(v_a_2330_, 0);
                        crate::leanh::lean_inc(v_fst_2331_);
                        v_snd_2332_ = crate::leanh::lean_ctor_get(v_a_2330_, 1);
                        crate::leanh::lean_inc(v_snd_2332_);
                        crate::leanh::lean_dec(v_a_2330_);
                        v___x_2333_ = l_Lean_Meta_FVarSubst_apply(v_fst_2331_, v___x_2308_);
                        v___x_2334_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_snd_2332_, v___x_2333_, v___y_2321_);
                        v_isSharedCheck_2425_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2334_)) as u8;
                        if v_isSharedCheck_2425_ == 0 {
                            v_unused_2426_ = crate::leanh::lean_ctor_get(v___x_2334_, 0);
                            crate::leanh::lean_dec(v_unused_2426_);
                            v___x_2336_ = v___x_2334_;
                            v_isShared_2337_ = v_isSharedCheck_2425_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2334_);
                            v___x_2336_ = crate::leanh::lean_box(0);
                            v_isShared_2337_ = v_isSharedCheck_2425_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2326_);
                        crate::leanh::lean_dec(v_levelParams_2319_);
                        crate::leanh::lean_dec(v_thmName_2318_);
                        crate::leanh::lean_dec_ref(v_a_2316_);
                        crate::leanh::lean_dec_ref(v_a_2314_);
                        crate::leanh::lean_dec_ref(v_xs_2312_);
                        crate::leanh::lean_dec_ref(v_val_2310_);
                        crate::leanh::lean_dec(v_snd_2309_);
                        crate::leanh::lean_dec(v_fst_2307_);
                        crate::leanh::lean_dec_ref(v___x_2305_);
                        v_a_2427_ = crate::leanh::lean_ctor_get(v___x_2329_, 0);
                        v_isSharedCheck_2434_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2329_)) as u8;
                        if v_isSharedCheck_2434_ == 0 {
                            v___x_2429_ = v___x_2329_;
                            v_isShared_2430_ = v_isSharedCheck_2434_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2427_);
                            crate::leanh::lean_dec(v___x_2329_);
                            v___x_2429_ = crate::leanh::lean_box(0);
                            v_isShared_2430_ = v_isSharedCheck_2434_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_levelParams_2319_);
                    crate::leanh::lean_dec(v_thmName_2318_);
                    crate::leanh::lean_dec_ref(v_a_2316_);
                    crate::leanh::lean_dec_ref(v_a_2314_);
                    crate::leanh::lean_dec_ref(v_xs_2312_);
                    crate::leanh::lean_dec_ref(v_val_2310_);
                    crate::leanh::lean_dec(v_snd_2309_);
                    crate::leanh::lean_dec(v_fst_2307_);
                    crate::leanh::lean_dec_ref(v___x_2305_);
                    v_a_2435_ = crate::leanh::lean_ctor_get(v___x_2325_, 0);
                    v_isSharedCheck_2442_ = (!crate::leanh::lean_is_exclusive(v___x_2325_)) as u8;
                    if v_isSharedCheck_2442_ == 0 {
                        v___x_2437_ = v___x_2325_;
                        v_isShared_2438_ = v_isSharedCheck_2442_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2435_);
                        crate::leanh::lean_dec(v___x_2325_);
                        v___x_2437_ = crate::leanh::lean_box(0);
                        v_isShared_2438_ = v_isSharedCheck_2442_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2338_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1;
                if v_isShared_2337_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2336_, 1);
                    crate::leanh::lean_ctor_set(v___x_2336_, 0, v___x_2305_);
                    v___x_2340_ = v___x_2336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2305_);
                    v___x_2340_ = v_reuseFailAlloc_2424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2341_ = l_Lean_MVarId_note(
                    v_snd_2309_,
                    v___x_2338_,
                    v_a_2326_,
                    v___x_2340_,
                    v___y_2320_,
                    v___y_2321_,
                    v___y_2322_,
                    v___y_2323_,
                );
                if crate::leanh::lean_obj_tag(v___x_2341_) == 0 {
                    v_a_2342_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                    crate::leanh::lean_inc(v_a_2342_);
                    crate::leanh::lean_dec_ref_known(v___x_2341_, 1);
                    v_fst_2343_ = crate::leanh::lean_ctor_get(v_a_2342_, 0);
                    v_snd_2344_ = crate::leanh::lean_ctor_get(v_a_2342_, 1);
                    v_isSharedCheck_2415_ = (!crate::leanh::lean_is_exclusive(v_a_2342_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2346_ = v_a_2342_;
                        v_isShared_2347_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2344_);
                        crate::leanh::lean_inc(v_fst_2343_);
                        crate::leanh::lean_dec(v_a_2342_);
                        v___x_2346_ = crate::leanh::lean_box(0);
                        v_isShared_2347_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_levelParams_2319_);
                    crate::leanh::lean_dec(v_thmName_2318_);
                    crate::leanh::lean_dec_ref(v_a_2316_);
                    crate::leanh::lean_dec_ref(v_a_2314_);
                    crate::leanh::lean_dec_ref(v_xs_2312_);
                    crate::leanh::lean_dec_ref(v_val_2310_);
                    crate::leanh::lean_dec(v_fst_2307_);
                    v_a_2416_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                    v_isSharedCheck_2423_ = (!crate::leanh::lean_is_exclusive(v___x_2341_)) as u8;
                    if v_isSharedCheck_2423_ == 0 {
                        v___x_2418_ = v___x_2341_;
                        v_isShared_2419_ = v_isSharedCheck_2423_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2416_);
                        crate::leanh::lean_dec(v___x_2341_);
                        v___x_2418_ = crate::leanh::lean_box(0);
                        v_isShared_2419_ = v_isSharedCheck_2423_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                v_majorPos_2348_ = crate::leanh::lean_ctor_get(v_val_2310_, 1);
                v___x_2349_ = lean_array_get_borrowed(v___x_2311_, v_xs_2312_, v_majorPos_2348_);
                v___x_2350_ = l_Lean_Expr_fvarId_x21(v___x_2349_);
                v___x_2351_ = lean_mk_empty_array_with_capacity(v___x_2313_);
                v___x_2352_ = 0;
                v___x_2394_ = crate::leanh::lean_box(0);
                v___x_2395_ = l_Lean_MVarId_cases(
                    v_snd_2344_,
                    v___x_2350_,
                    v___x_2351_,
                    v___x_2352_,
                    v___x_2394_,
                    v___y_2320_,
                    v___y_2321_,
                    v___y_2322_,
                    v___y_2323_,
                );
                if crate::leanh::lean_obj_tag(v___x_2395_) == 0 {
                    v_a_2396_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                    crate::leanh::lean_inc(v_a_2396_);
                    crate::leanh::lean_dec_ref_known(v___x_2395_, 1);
                    v___x_2397_ = lean_array_get_size(v_a_2396_);
                    v___x_2398_ = lean_nat_dec_lt(v___x_2313_, v___x_2397_);
                    if v___x_2398_ == 0 {
                        crate::leanh::lean_dec(v_a_2396_);
                        crate::leanh::lean_dec(v_fst_2343_);
                        crate::leanh::lean_dec_ref(v_val_2310_);
                        crate::leanh::lean_dec(v_fst_2307_);
                        state = 4;
                        continue;
                    } else {
                        v___x_2399_ = crate::leanh::lean_box(0);
                        v___x_2400_ = lean_nat_dec_le(v___x_2397_, v___x_2397_);
                        if v___x_2400_ == 0 {
                            if v___x_2398_ == 0 {
                                crate::leanh::lean_dec(v_a_2396_);
                                crate::leanh::lean_dec(v_fst_2343_);
                                crate::leanh::lean_dec_ref(v_val_2310_);
                                crate::leanh::lean_dec(v_fst_2307_);
                                state = 4;
                                continue;
                            } else {
                                v___x_2401_ = 0usize;
                                v___x_2402_ = lean_usize_of_nat(v___x_2397_);
                                v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_val_2310_, v___x_2317_, v_fst_2307_, v_fst_2343_, v_a_2396_, v___x_2401_, v___x_2402_, v___x_2399_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
                                crate::leanh::lean_dec(v_a_2396_);
                                v___y_2393_ = v___x_2403_;
                                state = 12;
                                continue;
                            }
                        } else {
                            v___x_2404_ = 0usize;
                            v___x_2405_ = lean_usize_of_nat(v___x_2397_);
                            v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_val_2310_, v___x_2317_, v_fst_2307_, v_fst_2343_, v_a_2396_, v___x_2404_, v___x_2405_, v___x_2399_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
                            crate::leanh::lean_dec(v_a_2396_);
                            v___y_2393_ = v___x_2406_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2346_);
                    crate::leanh::lean_dec(v_fst_2343_);
                    crate::leanh::lean_dec(v_levelParams_2319_);
                    crate::leanh::lean_dec(v_thmName_2318_);
                    crate::leanh::lean_dec_ref(v_a_2316_);
                    crate::leanh::lean_dec_ref(v_a_2314_);
                    crate::leanh::lean_dec_ref(v_xs_2312_);
                    crate::leanh::lean_dec_ref(v_val_2310_);
                    crate::leanh::lean_dec(v_fst_2307_);
                    v_a_2407_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                    v_isSharedCheck_2414_ = (!crate::leanh::lean_is_exclusive(v___x_2395_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v___x_2409_ = v___x_2395_;
                        v_isShared_2410_ = v_isSharedCheck_2414_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2407_);
                        crate::leanh::lean_dec(v___x_2395_);
                        v___x_2409_ = crate::leanh::lean_box(0);
                        v_isShared_2410_ = v_isSharedCheck_2414_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2354_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(v_a_2314_, v___y_2321_);
                v_a_2355_ = crate::leanh::lean_ctor_get(v___x_2354_, 0);
                v_isSharedCheck_2391_ = (!crate::leanh::lean_is_exclusive(v___x_2354_)) as u8;
                if v_isSharedCheck_2391_ == 0 {
                    v___x_2357_ = v___x_2354_;
                    v_isShared_2358_ = v_isSharedCheck_2391_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2355_);
                    crate::leanh::lean_dec(v___x_2354_);
                    v___x_2357_ = crate::leanh::lean_box(0);
                    v_isShared_2358_ = v_isSharedCheck_2391_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2359_ = l_Array_append___redArg(v_xs_2312_, v_hyps_2315_);
                v___x_2360_ = 1;
                v___x_2361_ = l_Lean_Meta_mkForallFVars(
                    v___x_2359_,
                    v_a_2316_,
                    v___x_2352_,
                    v___x_2317_,
                    v___x_2317_,
                    v___x_2360_,
                    v___y_2320_,
                    v___y_2321_,
                    v___y_2322_,
                    v___y_2323_,
                );
                if crate::leanh::lean_obj_tag(v___x_2361_) == 0 {
                    v_a_2362_ = crate::leanh::lean_ctor_get(v___x_2361_, 0);
                    crate::leanh::lean_inc(v_a_2362_);
                    crate::leanh::lean_dec_ref_known(v___x_2361_, 1);
                    v___x_2363_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_2359_,
                        v_a_2355_,
                        v___x_2352_,
                        v___x_2317_,
                        v___x_2352_,
                        v___x_2317_,
                        v___x_2360_,
                        v___y_2320_,
                        v___y_2321_,
                        v___y_2322_,
                        v___y_2323_,
                    );
                    crate::leanh::lean_dec_ref(v___x_2359_);
                    if crate::leanh::lean_obj_tag(v___x_2363_) == 0 {
                        v_a_2364_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                        crate::leanh::lean_inc(v_a_2364_);
                        crate::leanh::lean_dec_ref_known(v___x_2363_, 1);
                        crate::leanh::lean_inc(v_thmName_2318_);
                        v___x_2365_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2365_, 0, v_thmName_2318_);
                        crate::leanh::lean_ctor_set(v___x_2365_, 1, v_levelParams_2319_);
                        crate::leanh::lean_ctor_set(v___x_2365_, 2, v_a_2362_);
                        v___x_2366_ = crate::leanh::lean_box(0);
                        if v_isShared_2347_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2346_, 1);
                            crate::leanh::lean_ctor_set(v___x_2346_, 1, v___x_2366_);
                            crate::leanh::lean_ctor_set(v___x_2346_, 0, v_thmName_2318_);
                            v___x_2368_ = v___x_2346_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2374_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_thmName_2318_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2366_);
                            v___x_2368_ = v_reuseFailAlloc_2374_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2362_);
                        crate::leanh::lean_del_object(v___x_2357_);
                        crate::leanh::lean_del_object(v___x_2346_);
                        crate::leanh::lean_dec(v_levelParams_2319_);
                        crate::leanh::lean_dec(v_thmName_2318_);
                        v_a_2375_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                        v_isSharedCheck_2382_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2363_)) as u8;
                        if v_isSharedCheck_2382_ == 0 {
                            v___x_2377_ = v___x_2363_;
                            v_isShared_2378_ = v_isSharedCheck_2382_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2375_);
                            crate::leanh::lean_dec(v___x_2363_);
                            v___x_2377_ = crate::leanh::lean_box(0);
                            v_isShared_2378_ = v_isSharedCheck_2382_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2359_);
                    crate::leanh::lean_del_object(v___x_2357_);
                    crate::leanh::lean_dec(v_a_2355_);
                    crate::leanh::lean_del_object(v___x_2346_);
                    crate::leanh::lean_dec(v_levelParams_2319_);
                    crate::leanh::lean_dec(v_thmName_2318_);
                    v_a_2383_ = crate::leanh::lean_ctor_get(v___x_2361_, 0);
                    v_isSharedCheck_2390_ = (!crate::leanh::lean_is_exclusive(v___x_2361_)) as u8;
                    if v_isSharedCheck_2390_ == 0 {
                        v___x_2385_ = v___x_2361_;
                        v_isShared_2386_ = v_isSharedCheck_2390_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2383_);
                        crate::leanh::lean_dec(v___x_2361_);
                        v___x_2385_ = crate::leanh::lean_box(0);
                        v_isShared_2386_ = v_isSharedCheck_2390_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2369_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2369_, 0, v___x_2365_);
                crate::leanh::lean_ctor_set(v___x_2369_, 1, v_a_2364_);
                crate::leanh::lean_ctor_set(v___x_2369_, 2, v___x_2368_);
                if v_isShared_2358_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2357_, 2);
                    crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2369_);
                    v___x_2371_ = v___x_2357_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2369_);
                    v___x_2371_ = v_reuseFailAlloc_2373_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2372_ = l_Lean_addDecl(v___x_2371_, v___x_2352_, v___y_2322_, v___y_2323_);
                return v___x_2372_;
            }
            8 => {
                if v_isShared_2378_ == 0 {
                    v___x_2380_ = v___x_2377_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
                    v___x_2380_ = v_reuseFailAlloc_2381_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2380_;
            }
            10 => {
                if v_isShared_2386_ == 0 {
                    v___x_2388_ = v___x_2385_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
                    v___x_2388_ = v_reuseFailAlloc_2389_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2388_;
            }
            12 => {
                if crate::leanh::lean_obj_tag(v___y_2393_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2393_, 1);
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_2346_);
                    crate::leanh::lean_dec(v_levelParams_2319_);
                    crate::leanh::lean_dec(v_thmName_2318_);
                    crate::leanh::lean_dec_ref(v_a_2316_);
                    crate::leanh::lean_dec_ref(v_a_2314_);
                    crate::leanh::lean_dec_ref(v_xs_2312_);
                    return v___y_2393_;
                }
            }
            13 => {
                if v_isShared_2410_ == 0 {
                    v___x_2412_ = v___x_2409_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
                    v___x_2412_ = v_reuseFailAlloc_2413_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2412_;
            }
            15 => {
                if v_isShared_2419_ == 0 {
                    v___x_2421_ = v___x_2418_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2421_;
            }
            17 => {
                if v_isShared_2430_ == 0 {
                    v___x_2432_ = v___x_2429_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
                    v___x_2432_ = v_reuseFailAlloc_2433_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2432_;
            }
            19 => {
                if v_isShared_2438_ == 0 {
                    v___x_2440_ = v___x_2437_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
                    v___x_2440_ = v_reuseFailAlloc_2441_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2444_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_fst_2445_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2446_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_snd_2447_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_val_2448_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2449_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_xs_2450_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2451_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_2452_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_hyps_2453_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_2454_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2455_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_thmName_2456_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_levelParams_2457_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2458_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2459_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2460_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2461_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2462_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_19520__boxed_2463_: u8 = 0;
    let mut v_res_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_19520__boxed_2463_ = (crate::leanh::lean_unbox(v___x_2455_) as u8);
    v_res_2464_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(v___x_2443_, v___x_2444_, v_fst_2445_, v___x_2446_, v_snd_2447_, v_val_2448_, v___x_2449_, v_xs_2450_, v___x_2451_, v_a_2452_, v_hyps_2453_, v_a_2454_, v___x_19520__boxed_2463_, v_thmName_2456_, v_levelParams_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
    crate::leanh::lean_dec(v___y_2461_);
    crate::leanh::lean_dec_ref(v___y_2460_);
    crate::leanh::lean_dec(v___y_2459_);
    crate::leanh::lean_dec_ref(v___y_2458_);
    crate::leanh::lean_dec_ref(v_hyps_2453_);
    crate::leanh::lean_dec(v___x_2451_);
    crate::leanh::lean_dec_ref(v___x_2449_);
    crate::leanh::lean_dec_ref(v___x_2446_);
    return v_res_2464_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0;
    v___x_2467_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2468_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1;
    v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0;
    v___x_2471_ = l_mkPanicMessageWithDecl(
        v___x_2470_,
        v___x_2469_,
        v___x_2468_,
        v___x_2467_,
        v___x_2466_,
    );
    return v___x_2471_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2;
    v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
    return v___x_2474_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(
    mut v___x_2488_: *mut crate::leanh::LeanObject,
    mut v_sparseCasesOnName_2489_: *mut crate::leanh::LeanObject,
    mut v___x_2490_: *mut crate::leanh::LeanObject,
    mut v_xs_2491_: *mut crate::leanh::LeanObject,
    mut v___x_2492_: *mut crate::leanh::LeanObject,
    mut v___x_2493_: *mut crate::leanh::LeanObject,
    mut v___x_2494_: *mut crate::leanh::LeanObject,
    mut v_val_2495_: *mut crate::leanh::LeanObject,
    mut v_thmName_2496_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2497_: *mut crate::leanh::LeanObject,
    mut v_hyps_2498_: *mut crate::leanh::LeanObject,
    mut v_x_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2535_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v_arg_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v_arg_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_a_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_a_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v_a_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_a_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_a_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2505_ = lean_array_get_size(v_hyps_2498_);
                v___x_2506_ = lean_nat_dec_eq(v___x_2505_, v___x_2488_);
                if v___x_2506_ == 0 {
                    crate::leanh::lean_dec_ref(v_hyps_2498_);
                    crate::leanh::lean_dec(v_levelParams_2497_);
                    crate::leanh::lean_dec(v_thmName_2496_);
                    crate::leanh::lean_dec_ref(v_val_2495_);
                    crate::leanh::lean_dec(v___x_2494_);
                    crate::leanh::lean_dec_ref(v___x_2493_);
                    crate::leanh::lean_dec_ref(v___x_2492_);
                    crate::leanh::lean_dec_ref(v_xs_2491_);
                    crate::leanh::lean_dec(v___x_2490_);
                    crate::leanh::lean_dec(v_sparseCasesOnName_2489_);
                    v___x_2507_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1_once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1);
                    v___x_2508_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v___x_2507_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
                    return v___x_2508_;
                } else {
                    v___x_2509_ = l_Lean_mkConst(v_sparseCasesOnName_2489_, v___x_2490_);
                    v___x_2510_ = l_Lean_mkAppN(v___x_2509_, v_xs_2491_);
                    v___x_2511_ = l_Lean_mkAppN(v___x_2492_, v_hyps_2498_);
                    v___x_2512_ = l_Lean_Meta_mkEq(
                        v___x_2510_,
                        v___x_2511_,
                        v___y_2500_,
                        v___y_2501_,
                        v___y_2502_,
                        v___y_2503_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2512_) == 0 {
                        v_a_2513_ = crate::leanh::lean_ctor_get(v___x_2512_, 0);
                        crate::leanh::lean_inc_n(v_a_2513_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2512_, 1);
                        v___x_2514_ = crate::leanh::lean_box(0);
                        v___x_2515_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v_a_2513_,
                            v___x_2514_,
                            v___y_2500_,
                            v___y_2501_,
                            v___y_2502_,
                            v___y_2503_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2515_) == 0 {
                            v_a_2516_ = crate::leanh::lean_ctor_get(v___x_2515_, 0);
                            crate::leanh::lean_inc(v_a_2516_);
                            crate::leanh::lean_dec_ref_known(v___x_2515_, 1);
                            v___x_2517_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2518_ = lean_array_get(v___x_2493_, v_hyps_2498_, v___x_2517_);
                            crate::leanh::lean_inc(v___y_2503_);
                            crate::leanh::lean_inc_ref(v___y_2502_);
                            crate::leanh::lean_inc(v___y_2501_);
                            crate::leanh::lean_inc_ref(v___y_2500_);
                            crate::leanh::lean_inc(v___x_2518_);
                            v___x_2519_ = lean_infer_type(
                                v___x_2518_,
                                v___y_2500_,
                                v___y_2501_,
                                v___y_2502_,
                                v___y_2503_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2519_) == 0 {
                                v_a_2520_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                                crate::leanh::lean_inc(v_a_2520_);
                                crate::leanh::lean_dec_ref_known(v___x_2519_, 1);
                                v___x_2540_ = l_Lean_Expr_cleanupAnnotations(v_a_2520_);
                                v___x_2541_ = l_Lean_Expr_isApp(v___x_2540_);
                                if v___x_2541_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2540_);
                                    crate::leanh::lean_dec(v_a_2516_);
                                    crate::leanh::lean_dec(v_a_2513_);
                                    crate::leanh::lean_dec_ref(v_hyps_2498_);
                                    crate::leanh::lean_dec(v_levelParams_2497_);
                                    crate::leanh::lean_dec(v_thmName_2496_);
                                    crate::leanh::lean_dec_ref(v_val_2495_);
                                    crate::leanh::lean_dec(v___x_2494_);
                                    crate::leanh::lean_dec_ref(v___x_2493_);
                                    crate::leanh::lean_dec_ref(v_xs_2491_);
                                    v___y_2522_ = v___y_2500_;
                                    v___y_2523_ = v___y_2501_;
                                    v___y_2524_ = v___y_2502_;
                                    v___y_2525_ = v___y_2503_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_2542_ = crate::leanh::lean_ctor_get(v___x_2540_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2542_);
                                    v___x_2543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2540_);
                                    v___x_2544_ = l_Lean_Expr_isApp(v___x_2543_);
                                    if v___x_2544_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2543_);
                                        crate::leanh::lean_dec_ref(v_arg_2542_);
                                        crate::leanh::lean_dec(v_a_2516_);
                                        crate::leanh::lean_dec(v_a_2513_);
                                        crate::leanh::lean_dec_ref(v_hyps_2498_);
                                        crate::leanh::lean_dec(v_levelParams_2497_);
                                        crate::leanh::lean_dec(v_thmName_2496_);
                                        crate::leanh::lean_dec_ref(v_val_2495_);
                                        crate::leanh::lean_dec(v___x_2494_);
                                        crate::leanh::lean_dec_ref(v___x_2493_);
                                        crate::leanh::lean_dec_ref(v_xs_2491_);
                                        v___y_2522_ = v___y_2500_;
                                        v___y_2523_ = v___y_2501_;
                                        v___y_2524_ = v___y_2502_;
                                        v___y_2525_ = v___y_2503_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_2545_ = crate::leanh::lean_ctor_get(v___x_2543_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_2545_);
                                        v___x_2546_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2543_);
                                        v___x_2547_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6;
                                        v___x_2548_ =
                                            l_Lean_Expr_isConstOf(v___x_2546_, v___x_2547_);
                                        crate::leanh::lean_dec_ref(v___x_2546_);
                                        if v___x_2548_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_2545_);
                                            crate::leanh::lean_dec_ref(v_arg_2542_);
                                            crate::leanh::lean_dec(v_a_2516_);
                                            crate::leanh::lean_dec(v_a_2513_);
                                            crate::leanh::lean_dec_ref(v_hyps_2498_);
                                            crate::leanh::lean_dec(v_levelParams_2497_);
                                            crate::leanh::lean_dec(v_thmName_2496_);
                                            crate::leanh::lean_dec_ref(v_val_2495_);
                                            crate::leanh::lean_dec(v___x_2494_);
                                            crate::leanh::lean_dec_ref(v___x_2493_);
                                            crate::leanh::lean_dec_ref(v_xs_2491_);
                                            v___y_2522_ = v___y_2500_;
                                            v___y_2523_ = v___y_2501_;
                                            v___y_2524_ = v___y_2502_;
                                            v___y_2525_ = v___y_2503_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_2549_ = l_Lean_Expr_mvarId_x21(v_a_2516_);
                                            v___x_2550_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8;
                                            v___x_2551_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9;
                                            crate::leanh::lean_inc(v___x_2494_);
                                            v___x_2552_ = l_Lean_mkConst(v___x_2551_, v___x_2494_);
                                            v___x_2553_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11;
                                            v___x_2554_ = l_Lean_MVarId_assertExt(
                                                v___x_2549_,
                                                v___x_2550_,
                                                v___x_2552_,
                                                v_arg_2542_,
                                                v___x_2553_,
                                                v___y_2500_,
                                                v___y_2501_,
                                                v___y_2502_,
                                                v___y_2503_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2554_) == 0 {
                                                v_a_2555_ =
                                                    crate::leanh::lean_ctor_get(v___x_2554_, 0);
                                                crate::leanh::lean_inc(v_a_2555_);
                                                crate::leanh::lean_dec_ref_known(v___x_2554_, 1);
                                                v___x_2556_ = l_Lean_Meta_intro1Core(
                                                    v_a_2555_,
                                                    v___x_2548_,
                                                    v___y_2500_,
                                                    v___y_2501_,
                                                    v___y_2502_,
                                                    v___y_2503_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_2556_) == 0 {
                                                    v_a_2557_ =
                                                        crate::leanh::lean_ctor_get(v___x_2556_, 0);
                                                    crate::leanh::lean_inc(v_a_2557_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2556_,
                                                        1,
                                                    );
                                                    v_fst_2558_ =
                                                        crate::leanh::lean_ctor_get(v_a_2557_, 0);
                                                    crate::leanh::lean_inc(v_fst_2558_);
                                                    v_snd_2559_ =
                                                        crate::leanh::lean_ctor_get(v_a_2557_, 1);
                                                    crate::leanh::lean_inc(v_snd_2559_);
                                                    crate::leanh::lean_dec(v_a_2557_);
                                                    v___x_2560_ = l_Lean_Meta_intro1Core(
                                                        v_snd_2559_,
                                                        v___x_2548_,
                                                        v___y_2500_,
                                                        v___y_2501_,
                                                        v___y_2502_,
                                                        v___y_2503_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_2560_) == 0
                                                    {
                                                        v_a_2561_ = crate::leanh::lean_ctor_get(
                                                            v___x_2560_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_2561_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2560_,
                                                            1,
                                                        );
                                                        v_fst_2562_ = crate::leanh::lean_ctor_get(
                                                            v_a_2561_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_fst_2562_);
                                                        v_snd_2563_ = crate::leanh::lean_ctor_get(
                                                            v_a_2561_, 1,
                                                        );
                                                        crate::leanh::lean_inc_n(v_snd_2563_, 2);
                                                        crate::leanh::lean_dec(v_a_2561_);
                                                        v___x_2564_ = l_Lean_mkConst(
                                                            v___x_2547_,
                                                            v___x_2494_,
                                                        );
                                                        v___x_2565_ = l_Lean_mkFVar(v_fst_2558_);
                                                        v___x_2566_ = l_Lean_mkAppB(
                                                            v___x_2564_,
                                                            v_arg_2545_,
                                                            v___x_2565_,
                                                        );
                                                        v___x_2567_ = crate::leanh::lean_box(
                                                            (v___x_2548_) as usize,
                                                        );
                                                        v___f_2568_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed as *mut core::ffi::c_void, 20, 15);
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            0,
                                                            v___x_2566_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            1,
                                                            v___x_2514_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            2,
                                                            v_fst_2562_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            3,
                                                            v___x_2518_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            4,
                                                            v_snd_2563_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            5,
                                                            v_val_2495_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            6,
                                                            v___x_2493_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            7,
                                                            v_xs_2491_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            8,
                                                            v___x_2517_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            9,
                                                            v_a_2516_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            10,
                                                            v_hyps_2498_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            11,
                                                            v_a_2513_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            12,
                                                            v___x_2567_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            13,
                                                            v_thmName_2496_,
                                                        );
                                                        crate::leanh::lean_closure_set(
                                                            v___f_2568_,
                                                            14,
                                                            v_levelParams_2497_,
                                                        );
                                                        v___x_2569_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_snd_2563_, v___f_2568_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
                                                        return v___x_2569_;
                                                    } else {
                                                        crate::leanh::lean_dec(v_fst_2558_);
                                                        crate::leanh::lean_dec_ref(v_arg_2545_);
                                                        crate::leanh::lean_dec(v___x_2518_);
                                                        crate::leanh::lean_dec(v_a_2516_);
                                                        crate::leanh::lean_dec(v_a_2513_);
                                                        crate::leanh::lean_dec_ref(v_hyps_2498_);
                                                        crate::leanh::lean_dec(v_levelParams_2497_);
                                                        crate::leanh::lean_dec(v_thmName_2496_);
                                                        crate::leanh::lean_dec_ref(v_val_2495_);
                                                        crate::leanh::lean_dec(v___x_2494_);
                                                        crate::leanh::lean_dec_ref(v___x_2493_);
                                                        crate::leanh::lean_dec_ref(v_xs_2491_);
                                                        v_a_2570_ = crate::leanh::lean_ctor_get(
                                                            v___x_2560_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2577_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2560_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2577_ == 0 {
                                                            v___x_2572_ = v___x_2560_;
                                                            v_isShared_2573_ =
                                                                v_isSharedCheck_2577_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2570_);
                                                            crate::leanh::lean_dec(v___x_2560_);
                                                            v___x_2572_ = crate::leanh::lean_box(0);
                                                            v_isShared_2573_ =
                                                                v_isSharedCheck_2577_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_2545_);
                                                    crate::leanh::lean_dec(v___x_2518_);
                                                    crate::leanh::lean_dec(v_a_2516_);
                                                    crate::leanh::lean_dec(v_a_2513_);
                                                    crate::leanh::lean_dec_ref(v_hyps_2498_);
                                                    crate::leanh::lean_dec(v_levelParams_2497_);
                                                    crate::leanh::lean_dec(v_thmName_2496_);
                                                    crate::leanh::lean_dec_ref(v_val_2495_);
                                                    crate::leanh::lean_dec(v___x_2494_);
                                                    crate::leanh::lean_dec_ref(v___x_2493_);
                                                    crate::leanh::lean_dec_ref(v_xs_2491_);
                                                    v_a_2578_ =
                                                        crate::leanh::lean_ctor_get(v___x_2556_, 0);
                                                    v_isSharedCheck_2585_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2556_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2585_ == 0 {
                                                        v___x_2580_ = v___x_2556_;
                                                        v_isShared_2581_ = v_isSharedCheck_2585_;
                                                        state = 6;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2578_);
                                                        crate::leanh::lean_dec(v___x_2556_);
                                                        v___x_2580_ = crate::leanh::lean_box(0);
                                                        v_isShared_2581_ = v_isSharedCheck_2585_;
                                                        state = 6;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_arg_2545_);
                                                crate::leanh::lean_dec(v___x_2518_);
                                                crate::leanh::lean_dec(v_a_2516_);
                                                crate::leanh::lean_dec(v_a_2513_);
                                                crate::leanh::lean_dec_ref(v_hyps_2498_);
                                                crate::leanh::lean_dec(v_levelParams_2497_);
                                                crate::leanh::lean_dec(v_thmName_2496_);
                                                crate::leanh::lean_dec_ref(v_val_2495_);
                                                crate::leanh::lean_dec(v___x_2494_);
                                                crate::leanh::lean_dec_ref(v___x_2493_);
                                                crate::leanh::lean_dec_ref(v_xs_2491_);
                                                v_a_2586_ =
                                                    crate::leanh::lean_ctor_get(v___x_2554_, 0);
                                                v_isSharedCheck_2593_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2554_))
                                                        as u8;
                                                if v_isSharedCheck_2593_ == 0 {
                                                    v___x_2588_ = v___x_2554_;
                                                    v_isShared_2589_ = v_isSharedCheck_2593_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2586_);
                                                    crate::leanh::lean_dec(v___x_2554_);
                                                    v___x_2588_ = crate::leanh::lean_box(0);
                                                    v_isShared_2589_ = v_isSharedCheck_2593_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2518_);
                                crate::leanh::lean_dec(v_a_2516_);
                                crate::leanh::lean_dec(v_a_2513_);
                                crate::leanh::lean_dec_ref(v_hyps_2498_);
                                crate::leanh::lean_dec(v_levelParams_2497_);
                                crate::leanh::lean_dec(v_thmName_2496_);
                                crate::leanh::lean_dec_ref(v_val_2495_);
                                crate::leanh::lean_dec(v___x_2494_);
                                crate::leanh::lean_dec_ref(v___x_2493_);
                                crate::leanh::lean_dec_ref(v_xs_2491_);
                                v_a_2594_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                                v_isSharedCheck_2601_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2519_)) as u8;
                                if v_isSharedCheck_2601_ == 0 {
                                    v___x_2596_ = v___x_2519_;
                                    v_isShared_2597_ = v_isSharedCheck_2601_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2594_);
                                    crate::leanh::lean_dec(v___x_2519_);
                                    v___x_2596_ = crate::leanh::lean_box(0);
                                    v_isShared_2597_ = v_isSharedCheck_2601_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2513_);
                            crate::leanh::lean_dec_ref(v_hyps_2498_);
                            crate::leanh::lean_dec(v_levelParams_2497_);
                            crate::leanh::lean_dec(v_thmName_2496_);
                            crate::leanh::lean_dec_ref(v_val_2495_);
                            crate::leanh::lean_dec(v___x_2494_);
                            crate::leanh::lean_dec_ref(v___x_2493_);
                            crate::leanh::lean_dec_ref(v_xs_2491_);
                            v_a_2602_ = crate::leanh::lean_ctor_get(v___x_2515_, 0);
                            v_isSharedCheck_2609_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2515_)) as u8;
                            if v_isSharedCheck_2609_ == 0 {
                                v___x_2604_ = v___x_2515_;
                                v_isShared_2605_ = v_isSharedCheck_2609_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2602_);
                                crate::leanh::lean_dec(v___x_2515_);
                                v___x_2604_ = crate::leanh::lean_box(0);
                                v_isShared_2605_ = v_isSharedCheck_2609_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_hyps_2498_);
                        crate::leanh::lean_dec(v_levelParams_2497_);
                        crate::leanh::lean_dec(v_thmName_2496_);
                        crate::leanh::lean_dec_ref(v_val_2495_);
                        crate::leanh::lean_dec(v___x_2494_);
                        crate::leanh::lean_dec_ref(v___x_2493_);
                        crate::leanh::lean_dec_ref(v_xs_2491_);
                        v_a_2610_ = crate::leanh::lean_ctor_get(v___x_2512_, 0);
                        v_isSharedCheck_2617_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2512_)) as u8;
                        if v_isSharedCheck_2617_ == 0 {
                            v___x_2612_ = v___x_2512_;
                            v_isShared_2613_ = v_isSharedCheck_2617_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2610_);
                            crate::leanh::lean_dec(v___x_2512_);
                            v___x_2612_ = crate::leanh::lean_box(0);
                            v_isShared_2613_ = v_isSharedCheck_2617_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2525_);
                crate::leanh::lean_inc_ref(v___y_2524_);
                crate::leanh::lean_inc(v___y_2523_);
                crate::leanh::lean_inc_ref(v___y_2522_);
                v___x_2526_ = lean_infer_type(
                    v___x_2518_,
                    v___y_2522_,
                    v___y_2523_,
                    v___y_2524_,
                    v___y_2525_,
                );
                if crate::leanh::lean_obj_tag(v___x_2526_) == 0 {
                    v_a_2527_ = crate::leanh::lean_ctor_get(v___x_2526_, 0);
                    crate::leanh::lean_inc(v_a_2527_);
                    crate::leanh::lean_dec_ref_known(v___x_2526_, 1);
                    v___x_2528_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3_once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3);
                    v___x_2529_ = l_Lean_MessageData_ofExpr(v_a_2527_);
                    v___x_2530_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2530_, 0, v___x_2528_);
                    crate::leanh::lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                    v___x_2531_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_2530_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
                    return v___x_2531_;
                } else {
                    v_a_2532_ = crate::leanh::lean_ctor_get(v___x_2526_, 0);
                    v_isSharedCheck_2539_ = (!crate::leanh::lean_is_exclusive(v___x_2526_)) as u8;
                    if v_isSharedCheck_2539_ == 0 {
                        v___x_2534_ = v___x_2526_;
                        v_isShared_2535_ = v_isSharedCheck_2539_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2532_);
                        crate::leanh::lean_dec(v___x_2526_);
                        v___x_2534_ = crate::leanh::lean_box(0);
                        v_isShared_2535_ = v_isSharedCheck_2539_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2535_ == 0 {
                    v___x_2537_ = v___x_2534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
                    v___x_2537_ = v_reuseFailAlloc_2538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2537_;
            }
            4 => {
                if v_isShared_2573_ == 0 {
                    v___x_2575_ = v___x_2572_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
                    v___x_2575_ = v_reuseFailAlloc_2576_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2575_;
            }
            6 => {
                if v_isShared_2581_ == 0 {
                    v___x_2583_ = v___x_2580_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2583_;
            }
            8 => {
                if v_isShared_2589_ == 0 {
                    v___x_2591_ = v___x_2588_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
                    v___x_2591_ = v_reuseFailAlloc_2592_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2591_;
            }
            10 => {
                if v_isShared_2597_ == 0 {
                    v___x_2599_ = v___x_2596_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
                    v___x_2599_ = v_reuseFailAlloc_2600_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2599_;
            }
            12 => {
                if v_isShared_2605_ == 0 {
                    v___x_2607_ = v___x_2604_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
                    v___x_2607_ = v_reuseFailAlloc_2608_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2607_;
            }
            14 => {
                if v_isShared_2613_ == 0 {
                    v___x_2615_ = v___x_2612_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
                    v___x_2615_ = v_reuseFailAlloc_2616_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2618_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_sparseCasesOnName_2619_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2620_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_xs_2621_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2622_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2623_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2624_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_val_2625_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_thmName_2626_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_levelParams_2627_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_hyps_2628_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_x_2629_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2630_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2631_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2632_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2633_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2634_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2635_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(v___x_2618_, v_sparseCasesOnName_2619_, v___x_2620_, v_xs_2621_, v___x_2622_, v___x_2623_, v___x_2624_, v_val_2625_, v_thmName_2626_, v_levelParams_2627_, v_hyps_2628_, v_x_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
    crate::leanh::lean_dec(v___y_2633_);
    crate::leanh::lean_dec_ref(v___y_2632_);
    crate::leanh::lean_dec(v___y_2631_);
    crate::leanh::lean_dec_ref(v___y_2630_);
    crate::leanh::lean_dec_ref(v_x_2629_);
    crate::leanh::lean_dec(v___x_2618_);
    return v_res_2635_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(
    mut v___x_2636_: *mut crate::leanh::LeanObject,
    mut v_sparseCasesOnName_2637_: *mut crate::leanh::LeanObject,
    mut v___x_2638_: *mut crate::leanh::LeanObject,
    mut v___x_2639_: *mut crate::leanh::LeanObject,
    mut v_val_2640_: *mut crate::leanh::LeanObject,
    mut v_thmName_2641_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2642_: *mut crate::leanh::LeanObject,
    mut v_xs_2643_: *mut crate::leanh::LeanObject,
    mut v_x_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: u8 = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2650_ = lean_array_get_size(v_xs_2643_);
                v___x_2651_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2652_ = lean_nat_sub(v___x_2650_, v___x_2651_);
                v___x_2653_ = lean_array_get(v___x_2636_, v_xs_2643_, v___x_2652_);
                crate::leanh::lean_dec(v___x_2652_);
                crate::leanh::lean_inc(v___y_2648_);
                crate::leanh::lean_inc_ref(v___y_2647_);
                crate::leanh::lean_inc(v___y_2646_);
                crate::leanh::lean_inc_ref(v___y_2645_);
                crate::leanh::lean_inc(v___x_2653_);
                v___x_2654_ = lean_infer_type(
                    v___x_2653_,
                    v___y_2645_,
                    v___y_2646_,
                    v___y_2647_,
                    v___y_2648_,
                );
                if crate::leanh::lean_obj_tag(v___x_2654_) == 0 {
                    v_a_2655_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
                    crate::leanh::lean_inc(v_a_2655_);
                    crate::leanh::lean_dec_ref_known(v___x_2654_, 1);
                    v___f_2656_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed as *mut core::ffi::c_void, 17, 10);
                    crate::leanh::lean_closure_set(v___f_2656_, 0, v___x_2651_);
                    crate::leanh::lean_closure_set(v___f_2656_, 1, v_sparseCasesOnName_2637_);
                    crate::leanh::lean_closure_set(v___f_2656_, 2, v___x_2638_);
                    crate::leanh::lean_closure_set(v___f_2656_, 3, v_xs_2643_);
                    crate::leanh::lean_closure_set(v___f_2656_, 4, v___x_2653_);
                    crate::leanh::lean_closure_set(v___f_2656_, 5, v___x_2636_);
                    crate::leanh::lean_closure_set(v___f_2656_, 6, v___x_2639_);
                    crate::leanh::lean_closure_set(v___f_2656_, 7, v_val_2640_);
                    crate::leanh::lean_closure_set(v___f_2656_, 8, v_thmName_2641_);
                    crate::leanh::lean_closure_set(v___f_2656_, 9, v_levelParams_2642_);
                    v___x_2657_ = 0;
                    v___x_2658_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_a_2655_, v___f_2656_, v___x_2657_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
                    return v___x_2658_;
                } else {
                    crate::leanh::lean_dec(v___x_2653_);
                    crate::leanh::lean_dec_ref(v_xs_2643_);
                    crate::leanh::lean_dec(v_levelParams_2642_);
                    crate::leanh::lean_dec(v_thmName_2641_);
                    crate::leanh::lean_dec_ref(v_val_2640_);
                    crate::leanh::lean_dec(v___x_2639_);
                    crate::leanh::lean_dec(v___x_2638_);
                    crate::leanh::lean_dec(v_sparseCasesOnName_2637_);
                    crate::leanh::lean_dec_ref(v___x_2636_);
                    v_a_2659_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
                    v_isSharedCheck_2666_ = (!crate::leanh::lean_is_exclusive(v___x_2654_)) as u8;
                    if v_isSharedCheck_2666_ == 0 {
                        v___x_2661_ = v___x_2654_;
                        v_isShared_2662_ = v_isSharedCheck_2666_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2659_);
                        crate::leanh::lean_dec(v___x_2654_);
                        v___x_2661_ = crate::leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2666_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2662_ == 0 {
                    v___x_2664_ = v___x_2661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
                    v___x_2664_ = v_reuseFailAlloc_2665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed(
    mut v___x_2667_: *mut crate::leanh::LeanObject,
    mut v_sparseCasesOnName_2668_: *mut crate::leanh::LeanObject,
    mut v___x_2669_: *mut crate::leanh::LeanObject,
    mut v___x_2670_: *mut crate::leanh::LeanObject,
    mut v_val_2671_: *mut crate::leanh::LeanObject,
    mut v_thmName_2672_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2673_: *mut crate::leanh::LeanObject,
    mut v_xs_2674_: *mut crate::leanh::LeanObject,
    mut v_x_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
    mut v___y_2678_: *mut crate::leanh::LeanObject,
    mut v___y_2679_: *mut crate::leanh::LeanObject,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2681_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(v___x_2667_, v_sparseCasesOnName_2668_, v___x_2669_, v___x_2670_, v_val_2671_, v_thmName_2672_, v_levelParams_2673_, v_xs_2674_, v_x_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
    crate::leanh::lean_dec(v___y_2679_);
    crate::leanh::lean_dec_ref(v___y_2678_);
    crate::leanh::lean_dec(v___y_2677_);
    crate::leanh::lean_dec_ref(v___y_2676_);
    crate::leanh::lean_dec_ref(v_x_2675_);
    return v_res_2681_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(
    mut v_ref_2682_: *mut crate::leanh::LeanObject,
    mut v_msg_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2701_: u8 = 0;
    let mut v_cancelTk_x3f_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2703_: u8 = 0;
    let mut v_inheritedTraceOptions_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2689_ = crate::leanh::lean_ctor_get(v___y_2686_, 0);
    v_fileMap_2690_ = crate::leanh::lean_ctor_get(v___y_2686_, 1);
    v_options_2691_ = crate::leanh::lean_ctor_get(v___y_2686_, 2);
    v_currRecDepth_2692_ = crate::leanh::lean_ctor_get(v___y_2686_, 3);
    v_maxRecDepth_2693_ = crate::leanh::lean_ctor_get(v___y_2686_, 4);
    v_ref_2694_ = crate::leanh::lean_ctor_get(v___y_2686_, 5);
    v_currNamespace_2695_ = crate::leanh::lean_ctor_get(v___y_2686_, 6);
    v_openDecls_2696_ = crate::leanh::lean_ctor_get(v___y_2686_, 7);
    v_initHeartbeats_2697_ = crate::leanh::lean_ctor_get(v___y_2686_, 8);
    v_maxHeartbeats_2698_ = crate::leanh::lean_ctor_get(v___y_2686_, 9);
    v_quotContext_2699_ = crate::leanh::lean_ctor_get(v___y_2686_, 10);
    v_currMacroScope_2700_ = crate::leanh::lean_ctor_get(v___y_2686_, 11);
    v_diag_2701_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2686_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2702_ = crate::leanh::lean_ctor_get(v___y_2686_, 12);
    v_suppressElabErrors_2703_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2686_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2704_ = crate::leanh::lean_ctor_get(v___y_2686_, 13);
    v_ref_2705_ = l_Lean_replaceRef(v_ref_2682_, v_ref_2694_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2704_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2702_);
    crate::leanh::lean_inc(v_currMacroScope_2700_);
    crate::leanh::lean_inc(v_quotContext_2699_);
    crate::leanh::lean_inc(v_maxHeartbeats_2698_);
    crate::leanh::lean_inc(v_initHeartbeats_2697_);
    crate::leanh::lean_inc(v_openDecls_2696_);
    crate::leanh::lean_inc(v_currNamespace_2695_);
    crate::leanh::lean_inc(v_maxRecDepth_2693_);
    crate::leanh::lean_inc(v_currRecDepth_2692_);
    crate::leanh::lean_inc_ref(v_options_2691_);
    crate::leanh::lean_inc_ref(v_fileMap_2690_);
    crate::leanh::lean_inc_ref(v_fileName_2689_);
    v___x_2706_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2706_, 0, v_fileName_2689_);
    crate::leanh::lean_ctor_set(v___x_2706_, 1, v_fileMap_2690_);
    crate::leanh::lean_ctor_set(v___x_2706_, 2, v_options_2691_);
    crate::leanh::lean_ctor_set(v___x_2706_, 3, v_currRecDepth_2692_);
    crate::leanh::lean_ctor_set(v___x_2706_, 4, v_maxRecDepth_2693_);
    crate::leanh::lean_ctor_set(v___x_2706_, 5, v_ref_2705_);
    crate::leanh::lean_ctor_set(v___x_2706_, 6, v_currNamespace_2695_);
    crate::leanh::lean_ctor_set(v___x_2706_, 7, v_openDecls_2696_);
    crate::leanh::lean_ctor_set(v___x_2706_, 8, v_initHeartbeats_2697_);
    crate::leanh::lean_ctor_set(v___x_2706_, 9, v_maxHeartbeats_2698_);
    crate::leanh::lean_ctor_set(v___x_2706_, 10, v_quotContext_2699_);
    crate::leanh::lean_ctor_set(v___x_2706_, 11, v_currMacroScope_2700_);
    crate::leanh::lean_ctor_set(v___x_2706_, 12, v_cancelTk_x3f_2702_);
    crate::leanh::lean_ctor_set(v___x_2706_, 13, v_inheritedTraceOptions_2704_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2706_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2701_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2706_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2703_,
    );
    v___x_2707_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_2683_, v___y_2684_, v___y_2685_, v___x_2706_, v___y_2687_);
    crate::leanh::lean_dec_ref_known(v___x_2706_, 14);
    return v___x_2707_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg___boxed(
    mut v_ref_2708_: *mut crate::leanh::LeanObject,
    mut v_msg_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
    mut v___y_2712_: *mut crate::leanh::LeanObject,
    mut v___y_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2715_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(v_ref_2708_, v_msg_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
    crate::leanh::lean_dec(v___y_2713_);
    crate::leanh::lean_dec_ref(v___y_2712_);
    crate::leanh::lean_dec(v___y_2711_);
    crate::leanh::lean_dec_ref(v___y_2710_);
    crate::leanh::lean_dec(v_ref_2708_);
    return v_res_2715_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2716_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2717_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0);
    v___x_2718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2717_);
    return v___x_2718_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1);
    v___x_2720_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2721_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2721_, 0, v___x_2720_);
    crate::leanh::lean_ctor_set(v___x_2721_, 1, v___x_2720_);
    crate::leanh::lean_ctor_set(v___x_2721_, 2, v___x_2720_);
    crate::leanh::lean_ctor_set(v___x_2721_, 3, v___x_2720_);
    crate::leanh::lean_ctor_set(v___x_2721_, 4, v___x_2719_);
    crate::leanh::lean_ctor_set(v___x_2721_, 5, v___x_2719_);
    crate::leanh::lean_ctor_set(v___x_2721_, 6, v___x_2719_);
    crate::leanh::lean_ctor_set(v___x_2721_, 7, v___x_2719_);
    crate::leanh::lean_ctor_set(v___x_2721_, 8, v___x_2719_);
    crate::leanh::lean_ctor_set(v___x_2721_, 9, v___x_2719_);
    return v___x_2721_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2722_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2723_ = lean_mk_empty_array_with_capacity(v___x_2722_);
    v___x_2724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2723_);
    return v___x_2724_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: usize = 0;
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = 5usize;
    v___x_2726_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2727_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2728_ = lean_mk_empty_array_with_capacity(v___x_2727_);
    v___x_2729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3);
    v___x_2730_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2729_);
    crate::leanh::lean_ctor_set(v___x_2730_, 1, v___x_2728_);
    crate::leanh::lean_ctor_set(v___x_2730_, 2, v___x_2726_);
    crate::leanh::lean_ctor_set(v___x_2730_, 3, v___x_2726_);
    crate::leanh::lean_ctor_set_usize(v___x_2730_, 4, v___x_2725_);
    return v___x_2730_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2731_ = crate::leanh::lean_box(1);
    v___x_2732_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4);
    v___x_2733_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1);
    v___x_2734_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2733_);
    crate::leanh::lean_ctor_set(v___x_2734_, 1, v___x_2732_);
    crate::leanh::lean_ctor_set(v___x_2734_, 2, v___x_2731_);
    return v___x_2734_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6;
    v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
    return v___x_2737_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2739_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8;
    v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
    return v___x_2740_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10;
    v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
    return v___x_2743_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12;
    v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
    return v___x_2746_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14;
    v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
    return v___x_2749_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16;
    v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
    return v___x_2752_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18;
    v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
    return v___x_2755_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(
    mut v_msg_2756_: *mut crate::leanh::LeanObject,
    mut v_declHint_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    let mut v_isExporting_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: u8 = 0;
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2760_ = lean_st_ref_get(v___y_2758_);
                v_env_2761_ = crate::leanh::lean_ctor_get(v___x_2760_, 0);
                crate::leanh::lean_inc_ref(v_env_2761_);
                crate::leanh::lean_dec(v___x_2760_);
                v___x_2762_ = l_Lean_Name_isAnonymous(v_declHint_2757_);
                if v___x_2762_ == 0 {
                    v_isExporting_2763_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2761_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2763_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_2761_);
                        crate::leanh::lean_dec(v_declHint_2757_);
                        v___x_2764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2764_, 0, v_msg_2756_);
                        return v___x_2764_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_2761_);
                        v___x_2765_ = l_Lean_Environment_setExporting(v_env_2761_, v___x_2762_);
                        crate::leanh::lean_inc(v_declHint_2757_);
                        crate::leanh::lean_inc_ref(v___x_2765_);
                        v___x_2766_ = l_Lean_Environment_contains(
                            v___x_2765_,
                            v_declHint_2757_,
                            v_isExporting_2763_,
                        );
                        if v___x_2766_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2765_);
                            crate::leanh::lean_dec_ref(v_env_2761_);
                            crate::leanh::lean_dec(v_declHint_2757_);
                            v___x_2767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2767_, 0, v_msg_2756_);
                            return v___x_2767_;
                        } else {
                            v___x_2768_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2);
                            v___x_2769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5);
                            v___x_2770_ = l_Lean_Options_empty;
                            v___x_2771_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2771_, 0, v___x_2765_);
                            crate::leanh::lean_ctor_set(v___x_2771_, 1, v___x_2768_);
                            crate::leanh::lean_ctor_set(v___x_2771_, 2, v___x_2769_);
                            crate::leanh::lean_ctor_set(v___x_2771_, 3, v___x_2770_);
                            crate::leanh::lean_inc(v_declHint_2757_);
                            v___x_2772_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2757_, v___x_2762_);
                            v_c_2773_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_2773_, 0, v___x_2771_);
                            crate::leanh::lean_ctor_set(v_c_2773_, 1, v___x_2772_);
                            v___x_2774_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2761_,
                                v_declHint_2757_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2774_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_2761_);
                                crate::leanh::lean_dec(v_declHint_2757_);
                                v___x_2775_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7);
                                v___x_2776_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2776_, 0, v___x_2775_);
                                crate::leanh::lean_ctor_set(v___x_2776_, 1, v_c_2773_);
                                v___x_2777_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9);
                                v___x_2778_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2778_, 0, v___x_2776_);
                                crate::leanh::lean_ctor_set(v___x_2778_, 1, v___x_2777_);
                                v___x_2779_ = l_Lean_MessageData_note(v___x_2778_);
                                v___x_2780_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2780_, 0, v_msg_2756_);
                                crate::leanh::lean_ctor_set(v___x_2780_, 1, v___x_2779_);
                                v___x_2781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2780_);
                                return v___x_2781_;
                            } else {
                                v_val_2782_ = crate::leanh::lean_ctor_get(v___x_2774_, 0);
                                v_isSharedCheck_2817_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2774_)) as u8;
                                if v_isSharedCheck_2817_ == 0 {
                                    v___x_2784_ = v___x_2774_;
                                    v_isShared_2785_ = v_isSharedCheck_2817_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2782_);
                                    crate::leanh::lean_dec(v___x_2774_);
                                    v___x_2784_ = crate::leanh::lean_box(0);
                                    v_isShared_2785_ = v_isSharedCheck_2817_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2761_);
                    crate::leanh::lean_dec(v_declHint_2757_);
                    v___x_2818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2818_, 0, v_msg_2756_);
                    return v___x_2818_;
                }
            }
            1 => {
                v___x_2786_ = crate::leanh::lean_box(0);
                v___x_2787_ = l_Lean_Environment_header(v_env_2761_);
                crate::leanh::lean_dec_ref(v_env_2761_);
                v___x_2788_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2787_);
                v_mod_2789_ = lean_array_get(v___x_2786_, v___x_2788_, v_val_2782_);
                crate::leanh::lean_dec(v_val_2782_);
                crate::leanh::lean_dec_ref(v___x_2788_);
                v___x_2790_ = l_Lean_isPrivateName(v_declHint_2757_);
                crate::leanh::lean_dec(v_declHint_2757_);
                if v___x_2790_ == 0 {
                    v___x_2791_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11);
                    v___x_2792_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2792_, 0, v___x_2791_);
                    crate::leanh::lean_ctor_set(v___x_2792_, 1, v_c_2773_);
                    v___x_2793_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13);
                    v___x_2794_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2792_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v___x_2793_);
                    v___x_2795_ = l_Lean_MessageData_ofName(v_mod_2789_);
                    v___x_2796_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2794_);
                    crate::leanh::lean_ctor_set(v___x_2796_, 1, v___x_2795_);
                    v___x_2797_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15);
                    v___x_2798_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2798_, 0, v___x_2796_);
                    crate::leanh::lean_ctor_set(v___x_2798_, 1, v___x_2797_);
                    v___x_2799_ = l_Lean_MessageData_note(v___x_2798_);
                    v___x_2800_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2800_, 0, v_msg_2756_);
                    crate::leanh::lean_ctor_set(v___x_2800_, 1, v___x_2799_);
                    if v_isShared_2785_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2784_, 0);
                        crate::leanh::lean_ctor_set(v___x_2784_, 0, v___x_2800_);
                        v___x_2802_ = v___x_2784_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
                        v___x_2802_ = v_reuseFailAlloc_2803_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7);
                    v___x_2805_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2804_);
                    crate::leanh::lean_ctor_set(v___x_2805_, 1, v_c_2773_);
                    v___x_2806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17);
                    v___x_2807_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2807_, 0, v___x_2805_);
                    crate::leanh::lean_ctor_set(v___x_2807_, 1, v___x_2806_);
                    v___x_2808_ = l_Lean_MessageData_ofName(v_mod_2789_);
                    v___x_2809_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2809_, 0, v___x_2807_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 1, v___x_2808_);
                    v___x_2810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19);
                    v___x_2811_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2811_, 0, v___x_2809_);
                    crate::leanh::lean_ctor_set(v___x_2811_, 1, v___x_2810_);
                    v___x_2812_ = l_Lean_MessageData_note(v___x_2811_);
                    v___x_2813_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2813_, 0, v_msg_2756_);
                    crate::leanh::lean_ctor_set(v___x_2813_, 1, v___x_2812_);
                    if v_isShared_2785_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2784_, 0);
                        crate::leanh::lean_ctor_set(v___x_2784_, 0, v___x_2813_);
                        v___x_2815_ = v___x_2784_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
                        v___x_2815_ = v_reuseFailAlloc_2816_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2802_;
            }
            3 => {
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___boxed(
    mut v_msg_2819_: *mut crate::leanh::LeanObject,
    mut v_declHint_2820_: *mut crate::leanh::LeanObject,
    mut v___y_2821_: *mut crate::leanh::LeanObject,
    mut v___y_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2823_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(v_msg_2819_, v_declHint_2820_, v___y_2821_);
    crate::leanh::lean_dec(v___y_2821_);
    return v_res_2823_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(
    mut v_msg_2824_: *mut crate::leanh::LeanObject,
    mut v_declHint_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2831_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(v_msg_2824_, v_declHint_2825_, v___y_2829_);
                v_a_2832_ = crate::leanh::lean_ctor_get(v___x_2831_, 0);
                v_isSharedCheck_2841_ = (!crate::leanh::lean_is_exclusive(v___x_2831_)) as u8;
                if v_isSharedCheck_2841_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    v_isShared_2835_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2832_);
                    crate::leanh::lean_dec(v___x_2831_);
                    v___x_2834_ = crate::leanh::lean_box(0);
                    v_isShared_2835_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2836_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2837_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2837_, 0, v___x_2836_);
                crate::leanh::lean_ctor_set(v___x_2837_, 1, v_a_2832_);
                if v_isShared_2835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2834_, 0, v___x_2837_);
                    v___x_2839_ = v___x_2834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
                    v___x_2839_ = v_reuseFailAlloc_2840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14___boxed(
    mut v_msg_2842_: *mut crate::leanh::LeanObject,
    mut v_declHint_2843_: *mut crate::leanh::LeanObject,
    mut v___y_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
    mut v___y_2846_: *mut crate::leanh::LeanObject,
    mut v___y_2847_: *mut crate::leanh::LeanObject,
    mut v___y_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(v_msg_2842_, v_declHint_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
    crate::leanh::lean_dec(v___y_2847_);
    crate::leanh::lean_dec_ref(v___y_2846_);
    crate::leanh::lean_dec(v___y_2845_);
    crate::leanh::lean_dec_ref(v___y_2844_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_ref_2850_: *mut crate::leanh::LeanObject,
    mut v_msg_2851_: *mut crate::leanh::LeanObject,
    mut v_declHint_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
    mut v___y_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2858_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(v_msg_2851_, v_declHint_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
    v_a_2859_ = crate::leanh::lean_ctor_get(v___x_2858_, 0);
    crate::leanh::lean_inc(v_a_2859_);
    crate::leanh::lean_dec_ref(v___x_2858_);
    v___x_2860_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(v_ref_2850_, v_a_2859_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
    return v___x_2860_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg___boxed(
    mut v_ref_2861_: *mut crate::leanh::LeanObject,
    mut v_msg_2862_: *mut crate::leanh::LeanObject,
    mut v_declHint_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
    mut v___y_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(v_ref_2861_, v_msg_2862_, v_declHint_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
    crate::leanh::lean_dec(v___y_2867_);
    crate::leanh::lean_dec_ref(v___y_2866_);
    crate::leanh::lean_dec(v___y_2865_);
    crate::leanh::lean_dec_ref(v___y_2864_);
    crate::leanh::lean_dec(v_ref_2861_);
    return v_res_2869_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0;
    v___x_2872_ = l_Lean_stringToMessageData(v___x_2871_);
    return v___x_2872_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2;
    v___x_2875_ = l_Lean_stringToMessageData(v___x_2874_);
    return v___x_2875_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(
    mut v_ref_2876_: *mut crate::leanh::LeanObject,
    mut v_constName_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1);
    v___x_2884_ = 0;
    crate::leanh::lean_inc(v_constName_2877_);
    v___x_2885_ = l_Lean_MessageData_ofConstName(v_constName_2877_, v___x_2884_);
    v___x_2886_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2886_, 0, v___x_2883_);
    crate::leanh::lean_ctor_set(v___x_2886_, 1, v___x_2885_);
    v___x_2887_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3);
    v___x_2888_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2886_);
    crate::leanh::lean_ctor_set(v___x_2888_, 1, v___x_2887_);
    v___x_2889_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(v_ref_2876_, v___x_2888_, v_constName_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
    return v___x_2889_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___boxed(
    mut v_ref_2890_: *mut crate::leanh::LeanObject,
    mut v_constName_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2897_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_2890_, v_constName_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
    crate::leanh::lean_dec(v___y_2895_);
    crate::leanh::lean_dec_ref(v___y_2894_);
    crate::leanh::lean_dec(v___y_2893_);
    crate::leanh::lean_dec_ref(v___y_2892_);
    crate::leanh::lean_dec(v_ref_2890_);
    return v_res_2897_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(
    mut v_constName_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2904_ = crate::leanh::lean_ctor_get(v___y_2901_, 5);
    v___x_2905_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_2904_, v_constName_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
    return v___x_2905_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg___boxed(
    mut v_constName_2906_: *mut crate::leanh::LeanObject,
    mut v___y_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
    crate::leanh::lean_dec(v___y_2910_);
    crate::leanh::lean_dec_ref(v___y_2909_);
    crate::leanh::lean_dec(v___y_2908_);
    crate::leanh::lean_dec_ref(v___y_2907_);
    return v_res_2912_;
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(
    mut v_constName_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2919_ = lean_st_ref_get(v___y_2917_);
                v_env_2920_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
                crate::leanh::lean_inc_ref(v_env_2920_);
                crate::leanh::lean_dec(v___x_2919_);
                v___x_2921_ = 0;
                crate::leanh::lean_inc(v_constName_2913_);
                v___x_2922_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2920_,
                    v_constName_2913_,
                    v___x_2921_,
                );
                if crate::leanh::lean_obj_tag(v___x_2922_) == 0 {
                    v___x_2923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
                    return v___x_2923_;
                } else {
                    crate::leanh::lean_dec(v_constName_2913_);
                    v_val_2924_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2931_ = (!crate::leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2931_ == 0 {
                        v___x_2926_ = v___x_2922_;
                        v_isShared_2927_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2924_);
                        crate::leanh::lean_dec(v___x_2922_);
                        v___x_2926_ = crate::leanh::lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2927_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2926_, 0);
                    v___x_2929_ = v___x_2926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_val_2924_);
                    v___x_2929_ = v_reuseFailAlloc_2930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0___boxed(
    mut v_constName_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2938_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(v_constName_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
    crate::leanh::lean_dec(v___y_2936_);
    crate::leanh::lean_dec_ref(v___y_2935_);
    crate::leanh::lean_dec(v___y_2934_);
    crate::leanh::lean_dec_ref(v___y_2933_);
    return v_res_2938_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(
    mut v_a_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2939_) == 0 {
                    v___x_2941_ = l_List_reverse___redArg(v_a_2940_);
                    return v___x_2941_;
                } else {
                    v_head_2942_ = crate::leanh::lean_ctor_get(v_a_2939_, 0);
                    v_tail_2943_ = crate::leanh::lean_ctor_get(v_a_2939_, 1);
                    v_isSharedCheck_2952_ = (!crate::leanh::lean_is_exclusive(v_a_2939_)) as u8;
                    if v_isSharedCheck_2952_ == 0 {
                        v___x_2945_ = v_a_2939_;
                        v_isShared_2946_ = v_isSharedCheck_2952_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2943_);
                        crate::leanh::lean_inc(v_head_2942_);
                        crate::leanh::lean_dec(v_a_2939_);
                        v___x_2945_ = crate::leanh::lean_box(0);
                        v_isShared_2946_ = v_isSharedCheck_2952_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2947_ = l_Lean_mkLevelParam(v_head_2942_);
                if v_isShared_2946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2945_, 1, v_a_2940_);
                    crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2947_);
                    v___x_2949_ = v___x_2945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_a_2940_);
                    v___x_2949_ = v_reuseFailAlloc_2951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2939_ = v_tail_2943_;
                v_a_2940_ = v___x_2949_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0;
    v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
    return v___x_2955_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2;
    v___x_2958_ = l_Lean_stringToMessageData(v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(
    mut v_sparseCasesOnName_2959_: *mut crate::leanh::LeanObject,
    mut v_thmName_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_sparseCasesOnName_2959_);
                v___x_2966_ =
                    l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2959_, v_a_2964_);
                if crate::leanh::lean_obj_tag(v___x_2966_) == 0 {
                    v_a_2967_ = crate::leanh::lean_ctor_get(v___x_2966_, 0);
                    crate::leanh::lean_inc(v_a_2967_);
                    crate::leanh::lean_dec_ref_known(v___x_2966_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2967_) == 1 {
                        v_val_2968_ = crate::leanh::lean_ctor_get(v_a_2967_, 0);
                        crate::leanh::lean_inc(v_val_2968_);
                        crate::leanh::lean_dec_ref_known(v_a_2967_, 1);
                        crate::leanh::lean_inc(v_sparseCasesOnName_2959_);
                        v___x_2969_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(v_sparseCasesOnName_2959_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
                        if crate::leanh::lean_obj_tag(v___x_2969_) == 0 {
                            v_a_2970_ = crate::leanh::lean_ctor_get(v___x_2969_, 0);
                            crate::leanh::lean_inc(v_a_2970_);
                            crate::leanh::lean_dec_ref_known(v___x_2969_, 1);
                            v_levelParams_2971_ = crate::leanh::lean_ctor_get(v_a_2970_, 1);
                            crate::leanh::lean_inc_n(v_levelParams_2971_, 2);
                            v_type_2972_ = crate::leanh::lean_ctor_get(v_a_2970_, 2);
                            crate::leanh::lean_inc_ref(v_type_2972_);
                            crate::leanh::lean_dec(v_a_2970_);
                            v___x_2973_ = l_Lean_instInhabitedExpr;
                            v___x_2974_ = crate::leanh::lean_box(0);
                            v___x_2975_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(v_levelParams_2971_, v___x_2974_);
                            v___f_2976_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed as *mut core::ffi::c_void, 14, 7);
                            crate::leanh::lean_closure_set(v___f_2976_, 0, v___x_2973_);
                            crate::leanh::lean_closure_set(
                                v___f_2976_,
                                1,
                                v_sparseCasesOnName_2959_,
                            );
                            crate::leanh::lean_closure_set(v___f_2976_, 2, v___x_2975_);
                            crate::leanh::lean_closure_set(v___f_2976_, 3, v___x_2974_);
                            crate::leanh::lean_closure_set(v___f_2976_, 4, v_val_2968_);
                            crate::leanh::lean_closure_set(v___f_2976_, 5, v_thmName_2960_);
                            crate::leanh::lean_closure_set(v___f_2976_, 6, v_levelParams_2971_);
                            v___x_2977_ = 0;
                            v___x_2978_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_type_2972_, v___f_2976_, v___x_2977_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
                            return v___x_2978_;
                        } else {
                            crate::leanh::lean_dec(v_val_2968_);
                            crate::leanh::lean_dec(v_thmName_2960_);
                            crate::leanh::lean_dec(v_sparseCasesOnName_2959_);
                            v_a_2979_ = crate::leanh::lean_ctor_get(v___x_2969_, 0);
                            v_isSharedCheck_2986_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2969_)) as u8;
                            if v_isSharedCheck_2986_ == 0 {
                                v___x_2981_ = v___x_2969_;
                                v_isShared_2982_ = v_isSharedCheck_2986_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2979_);
                                crate::leanh::lean_dec(v___x_2969_);
                                v___x_2981_ = crate::leanh::lean_box(0);
                                v_isShared_2982_ = v_isSharedCheck_2986_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2967_);
                        crate::leanh::lean_dec(v_thmName_2960_);
                        v___x_2987_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1_once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1);
                        v___x_2988_ = l_Lean_MessageData_ofName(v_sparseCasesOnName_2959_);
                        v___x_2989_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2989_, 0, v___x_2987_);
                        crate::leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                        v___x_2990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3_once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3);
                        v___x_2991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2991_, 0, v___x_2989_);
                        crate::leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                        v___x_2992_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_2991_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
                        return v___x_2992_;
                    }
                } else {
                    crate::leanh::lean_dec(v_thmName_2960_);
                    crate::leanh::lean_dec(v_sparseCasesOnName_2959_);
                    v_a_2993_ = crate::leanh::lean_ctor_get(v___x_2966_, 0);
                    v_isSharedCheck_3000_ = (!crate::leanh::lean_is_exclusive(v___x_2966_)) as u8;
                    if v_isSharedCheck_3000_ == 0 {
                        v___x_2995_ = v___x_2966_;
                        v_isShared_2996_ = v_isSharedCheck_3000_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2993_);
                        crate::leanh::lean_dec(v___x_2966_);
                        v___x_2995_ = crate::leanh::lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3000_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2982_ == 0 {
                    v___x_2984_ = v___x_2981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
                    v___x_2984_ = v_reuseFailAlloc_2985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2984_;
            }
            3 => {
                if v_isShared_2996_ == 0 {
                    v___x_2998_ = v___x_2995_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
                    v___x_2998_ = v_reuseFailAlloc_2999_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed(
    mut v_sparseCasesOnName_3001_: *mut crate::leanh::LeanObject,
    mut v_thmName_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_a_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3008_ =
        l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(
            v_sparseCasesOnName_3001_,
            v_thmName_3002_,
            v_a_3003_,
            v_a_3004_,
            v_a_3005_,
            v_a_3006_,
        );
    crate::leanh::lean_dec(v_a_3006_);
    crate::leanh::lean_dec_ref(v_a_3005_);
    crate::leanh::lean_dec(v_a_3004_);
    crate::leanh::lean_dec_ref(v_a_3003_);
    return v_res_3008_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(
    mut v_00_u03b1_3009_: *mut crate::leanh::LeanObject,
    mut v_msg_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___boxed(
    mut v_00_u03b1_3017_: *mut crate::leanh::LeanObject,
    mut v_msg_3018_: *mut crate::leanh::LeanObject,
    mut v___y_3019_: *mut crate::leanh::LeanObject,
    mut v___y_3020_: *mut crate::leanh::LeanObject,
    mut v___y_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3024_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(v_00_u03b1_3017_, v_msg_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
    crate::leanh::lean_dec(v___y_3022_);
    crate::leanh::lean_dec_ref(v___y_3021_);
    crate::leanh::lean_dec(v___y_3020_);
    crate::leanh::lean_dec_ref(v___y_3019_);
    return v_res_3024_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(
    mut v_mvarId_3025_: *mut crate::leanh::LeanObject,
    mut v_val_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
    mut v___y_3029_: *mut crate::leanh::LeanObject,
    mut v___y_3030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_mvarId_3025_, v_val_3026_, v___y_3028_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___boxed(
    mut v_mvarId_3033_: *mut crate::leanh::LeanObject,
    mut v_val_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(v_mvarId_3033_, v_val_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
    crate::leanh::lean_dec(v___y_3038_);
    crate::leanh::lean_dec_ref(v___y_3037_);
    crate::leanh::lean_dec(v___y_3036_);
    crate::leanh::lean_dec_ref(v___y_3035_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(
    mut v_00_u03b1_3041_: *mut crate::leanh::LeanObject,
    mut v_constName_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
    return v___x_3048_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___boxed(
    mut v_00_u03b1_3049_: *mut crate::leanh::LeanObject,
    mut v_constName_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
    mut v___y_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(v_00_u03b1_3049_, v_constName_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
    crate::leanh::lean_dec(v___y_3054_);
    crate::leanh::lean_dec_ref(v___y_3053_);
    crate::leanh::lean_dec(v___y_3052_);
    crate::leanh::lean_dec_ref(v___y_3051_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6(
    mut v_00_u03b2_3057_: *mut crate::leanh::LeanObject,
    mut v_x_3058_: *mut crate::leanh::LeanObject,
    mut v_x_3059_: *mut crate::leanh::LeanObject,
    mut v_x_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(v_x_3058_, v_x_3059_, v_x_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(
    mut v_00_u03b1_3062_: *mut crate::leanh::LeanObject,
    mut v_ref_3063_: *mut crate::leanh::LeanObject,
    mut v_constName_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3070_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_3063_, v_constName_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
    return v___x_3070_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___boxed(
    mut v_00_u03b1_3071_: *mut crate::leanh::LeanObject,
    mut v_ref_3072_: *mut crate::leanh::LeanObject,
    mut v_constName_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3079_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(v_00_u03b1_3071_, v_ref_3072_, v_constName_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
    crate::leanh::lean_dec(v___y_3077_);
    crate::leanh::lean_dec_ref(v___y_3076_);
    crate::leanh::lean_dec(v___y_3075_);
    crate::leanh::lean_dec_ref(v___y_3074_);
    crate::leanh::lean_dec(v_ref_3072_);
    return v_res_3079_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(
    mut v_00_u03b2_3080_: *mut crate::leanh::LeanObject,
    mut v_x_3081_: *mut crate::leanh::LeanObject,
    mut v_x_3082_: usize,
    mut v_x_3083_: usize,
    mut v_x_3084_: *mut crate::leanh::LeanObject,
    mut v_x_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_3081_, v_x_3082_, v_x_3083_, v_x_3084_, v_x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___boxed(
    mut v_00_u03b2_3087_: *mut crate::leanh::LeanObject,
    mut v_x_3088_: *mut crate::leanh::LeanObject,
    mut v_x_3089_: *mut crate::leanh::LeanObject,
    mut v_x_3090_: *mut crate::leanh::LeanObject,
    mut v_x_3091_: *mut crate::leanh::LeanObject,
    mut v_x_3092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_20830__boxed_3093_: usize = 0;
    let mut v_x_20831__boxed_3094_: usize = 0;
    let mut v_res_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_20830__boxed_3093_ = crate::leanh::lean_unbox_usize(v_x_3089_);
    crate::leanh::lean_dec(v_x_3089_);
    v_x_20831__boxed_3094_ = crate::leanh::lean_unbox_usize(v_x_3090_);
    crate::leanh::lean_dec(v_x_3090_);
    v_res_3095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(v_00_u03b2_3087_, v_x_3088_, v_x_20830__boxed_3093_, v_x_20831__boxed_3094_, v_x_3091_, v_x_3092_);
    return v_res_3095_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b1_3096_: *mut crate::leanh::LeanObject,
    mut v_ref_3097_: *mut crate::leanh::LeanObject,
    mut v_msg_3098_: *mut crate::leanh::LeanObject,
    mut v_declHint_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(v_ref_3097_, v_msg_3098_, v_declHint_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
    return v___x_3105_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___boxed(
    mut v_00_u03b1_3106_: *mut crate::leanh::LeanObject,
    mut v_ref_3107_: *mut crate::leanh::LeanObject,
    mut v_msg_3108_: *mut crate::leanh::LeanObject,
    mut v_declHint_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3115_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12(v_00_u03b1_3106_, v_ref_3107_, v_msg_3108_, v_declHint_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
    crate::leanh::lean_dec(v___y_3113_);
    crate::leanh::lean_dec_ref(v___y_3112_);
    crate::leanh::lean_dec(v___y_3111_);
    crate::leanh::lean_dec_ref(v___y_3110_);
    crate::leanh::lean_dec(v_ref_3107_);
    return v_res_3115_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15(
    mut v_00_u03b2_3116_: *mut crate::leanh::LeanObject,
    mut v_n_3117_: *mut crate::leanh::LeanObject,
    mut v_k_3118_: *mut crate::leanh::LeanObject,
    mut v_v_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3120_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(v_n_3117_, v_k_3118_, v_v_3119_);
    return v___x_3120_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(
    mut v_00_u03b2_3121_: *mut crate::leanh::LeanObject,
    mut v_depth_3122_: usize,
    mut v_keys_3123_: *mut crate::leanh::LeanObject,
    mut v_vals_3124_: *mut crate::leanh::LeanObject,
    mut v_heq_3125_: *mut crate::leanh::LeanObject,
    mut v_i_3126_: *mut crate::leanh::LeanObject,
    mut v_entries_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_depth_3122_, v_keys_3123_, v_vals_3124_, v_i_3126_, v_entries_3127_);
    return v___x_3128_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___boxed(
    mut v_00_u03b2_3129_: *mut crate::leanh::LeanObject,
    mut v_depth_3130_: *mut crate::leanh::LeanObject,
    mut v_keys_3131_: *mut crate::leanh::LeanObject,
    mut v_vals_3132_: *mut crate::leanh::LeanObject,
    mut v_heq_3133_: *mut crate::leanh::LeanObject,
    mut v_i_3134_: *mut crate::leanh::LeanObject,
    mut v_entries_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3136_: usize = 0;
    let mut v_res_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3136_ = crate::leanh::lean_unbox_usize(v_depth_3130_);
    crate::leanh::lean_dec(v_depth_3130_);
    v_res_3137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(v_00_u03b2_3129_, v_depth_boxed_3136_, v_keys_3131_, v_vals_3132_, v_heq_3133_, v_i_3134_, v_entries_3135_);
    crate::leanh::lean_dec_ref(v_vals_3132_);
    crate::leanh::lean_dec_ref(v_keys_3131_);
    return v_res_3137_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16(
    mut v_msg_3138_: *mut crate::leanh::LeanObject,
    mut v_declHint_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(v_msg_3138_, v_declHint_3139_, v___y_3143_);
    return v___x_3145_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___boxed(
    mut v_msg_3146_: *mut crate::leanh::LeanObject,
    mut v_declHint_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16(v_msg_3146_, v_declHint_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
    crate::leanh::lean_dec(v___y_3151_);
    crate::leanh::lean_dec_ref(v___y_3150_);
    crate::leanh::lean_dec(v___y_3149_);
    crate::leanh::lean_dec_ref(v___y_3148_);
    return v_res_3153_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15(
    mut v_00_u03b1_3154_: *mut crate::leanh::LeanObject,
    mut v_ref_3155_: *mut crate::leanh::LeanObject,
    mut v_msg_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3162_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(v_ref_3155_, v_msg_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
    return v___x_3162_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___boxed(
    mut v_00_u03b1_3163_: *mut crate::leanh::LeanObject,
    mut v_ref_3164_: *mut crate::leanh::LeanObject,
    mut v_msg_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15(v_00_u03b1_3163_, v_ref_3164_, v_msg_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
    crate::leanh::lean_dec(v___y_3169_);
    crate::leanh::lean_dec_ref(v___y_3168_);
    crate::leanh::lean_dec(v___y_3167_);
    crate::leanh::lean_dec_ref(v___y_3166_);
    crate::leanh::lean_dec(v_ref_3164_);
    return v_res_3171_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18(
    mut v_00_u03b2_3172_: *mut crate::leanh::LeanObject,
    mut v_x_3173_: *mut crate::leanh::LeanObject,
    mut v_x_3174_: *mut crate::leanh::LeanObject,
    mut v_x_3175_: *mut crate::leanh::LeanObject,
    mut v_x_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3177_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(v_x_3173_, v_x_3174_, v_x_3175_, v_x_3176_);
    return v___x_3177_;
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnEq(
    mut v_sparseCasesOnName_3179_: *mut crate::leanh::LeanObject,
    mut v_a_3180_: *mut crate::leanh::LeanObject,
    mut v_a_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmName_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut v_unused_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3185_ = l_Lean_Meta_getSparseCasesOnEq___closed__0;
                crate::leanh::lean_inc_n(v_sparseCasesOnName_3179_, 2);
                v_thmName_3186_ =
                    l_Lean_Name_str___override(v_sparseCasesOnName_3179_, v___x_3185_);
                crate::leanh::lean_inc_n(v_thmName_3186_, 2);
                v___x_3187_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed as *mut core::ffi::c_void, 7, 2);
                crate::leanh::lean_closure_set(v___x_3187_, 0, v_sparseCasesOnName_3179_);
                crate::leanh::lean_closure_set(v___x_3187_, 1, v_thmName_3186_);
                v___x_3188_ = l_Lean_Meta_realizeConst(
                    v_sparseCasesOnName_3179_,
                    v_thmName_3186_,
                    v___x_3187_,
                    v_a_3180_,
                    v_a_3181_,
                    v_a_3182_,
                    v_a_3183_,
                );
                if crate::leanh::lean_obj_tag(v___x_3188_) == 0 {
                    v_isSharedCheck_3195_ = (!crate::leanh::lean_is_exclusive(v___x_3188_)) as u8;
                    if v_isSharedCheck_3195_ == 0 {
                        v_unused_3196_ = crate::leanh::lean_ctor_get(v___x_3188_, 0);
                        crate::leanh::lean_dec(v_unused_3196_);
                        v___x_3190_ = v___x_3188_;
                        v_isShared_3191_ = v_isSharedCheck_3195_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3188_);
                        v___x_3190_ = crate::leanh::lean_box(0);
                        v_isShared_3191_ = v_isSharedCheck_3195_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_thmName_3186_);
                    v_a_3197_ = crate::leanh::lean_ctor_get(v___x_3188_, 0);
                    v_isSharedCheck_3204_ = (!crate::leanh::lean_is_exclusive(v___x_3188_)) as u8;
                    if v_isSharedCheck_3204_ == 0 {
                        v___x_3199_ = v___x_3188_;
                        v_isShared_3200_ = v_isSharedCheck_3204_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3197_);
                        crate::leanh::lean_dec(v___x_3188_);
                        v___x_3199_ = crate::leanh::lean_box(0);
                        v_isShared_3200_ = v_isSharedCheck_3204_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3190_, 0, v_thmName_3186_);
                    v___x_3193_ = v___x_3190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_thmName_3186_);
                    v___x_3193_ = v_reuseFailAlloc_3194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3193_;
            }
            3 => {
                if v_isShared_3200_ == 0 {
                    v___x_3202_ = v___x_3199_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnEq___boxed(
    mut v_sparseCasesOnName_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_a_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Lean_Meta_getSparseCasesOnEq(
        v_sparseCasesOnName_3205_,
        v_a_3206_,
        v_a_3207_,
        v_a_3208_,
        v_a_3209_,
    );
    crate::leanh::lean_dec(v_a_3209_);
    crate::leanh::lean_dec_ref(v_a_3208_);
    crate::leanh::lean_dec(v_a_3207_);
    crate::leanh::lean_dec_ref(v_a_3206_);
    return v_res_3211_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(
    mut v_env_3212_: *mut crate::leanh::LeanObject,
    mut v_n_3213_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_n_3213_) == 1 {
        let mut v_pre_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3217_: u8 = 0;
        v_pre_3214_ = crate::leanh::lean_ctor_get(v_n_3213_, 0);
        crate::leanh::lean_inc(v_pre_3214_);
        v_str_3215_ = crate::leanh::lean_ctor_get(v_n_3213_, 1);
        crate::leanh::lean_inc_ref(v_str_3215_);
        crate::leanh::lean_dec_ref_known(v_n_3213_, 2);
        v___x_3216_ = l_Lean_Meta_getSparseCasesOnEq___closed__0;
        v___x_3217_ = lean_string_dec_eq(v_str_3215_, v___x_3216_);
        crate::leanh::lean_dec_ref(v_str_3215_);
        if v___x_3217_ == 0 {
            crate::leanh::lean_dec(v_pre_3214_);
            crate::leanh::lean_dec_ref(v_env_3212_);
            return v___x_3217_;
        } else {
            let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3218_ = l_Lean_Meta_getSparseCasesOnInfoCore(v_env_3212_, v_pre_3214_);
            if crate::leanh::lean_obj_tag(v___x_3218_) == 0 {
                let mut v___x_3219_: u8 = 0;
                v___x_3219_ = 0;
                return v___x_3219_;
            } else {
                crate::leanh::lean_dec_ref_known(v___x_3218_, 1);
                return v___x_3217_;
            }
        }
    } else {
        let mut v___x_3220_: u8 = 0;
        crate::leanh::lean_dec(v_n_3213_);
        crate::leanh::lean_dec_ref(v_env_3212_);
        v___x_3220_ = 0;
        return v___x_3220_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed(
    mut v_env_3221_: *mut crate::leanh::LeanObject,
    mut v_n_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: u8 = 0;
    let mut v_r_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(
        v_env_3221_,
        v_n_3222_,
    );
    v_r_3224_ = crate::leanh::lean_box((v_res_3223_) as usize);
    return v_r_3224_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_;
    v___x_3228_ = l_Lean_registerReservedNamePredicate(v___x_3227_);
    return v___x_3228_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2____boxed(
    mut v_a_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3230_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_();
    return v_res_3230_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(
    mut v_msg_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124__overap_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3236_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0;
    v___x_1124__overap_3237_ = lean_panic_fn_borrowed(v___f_3236_, v_msg_3232_);
    crate::leanh::lean_inc(v___y_3234_);
    crate::leanh::lean_inc_ref(v___y_3233_);
    v___x_3238_ = crate::leanh::lean_apply_3(
        v___x_1124__overap_3237_,
        v___y_3233_,
        v___y_3234_,
        crate::leanh::lean_box(0),
    );
    return v___x_3238_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___boxed(
    mut v_msg_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(v_msg_3239_, v___y_3240_, v___y_3241_);
    crate::leanh::lean_dec(v___y_3241_);
    crate::leanh::lean_dec_ref(v___y_3240_);
    return v_res_3243_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
    v___x_3247_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3248_ = crate::leanh::lean_unsigned_to_nat(97);
    v___x_3249_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
    v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0;
    v___x_3251_ = l_mkPanicMessageWithDecl(
        v___x_3250_,
        v___x_3249_,
        v___x_3248_,
        v___x_3247_,
        v___x_3246_,
    );
    return v___x_3251_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3252_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3254_, 0, v___x_3253_);
    return v___x_3254_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = crate::leanh::lean_box(1);
    v___x_3256_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4);
    v___x_3257_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3258_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3258_, 0, v___x_3257_);
    crate::leanh::lean_ctor_set(v___x_3258_, 1, v___x_3256_);
    crate::leanh::lean_ctor_set(v___x_3258_, 2, v___x_3255_);
    return v___x_3258_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3261_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3262_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3263_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3263_, 1, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3263_, 2, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3263_, 3, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3263_, 4, v___x_3261_);
    crate::leanh::lean_ctor_set(v___x_3263_, 5, v___x_3261_);
    crate::leanh::lean_ctor_set(v___x_3263_, 6, v___x_3261_);
    crate::leanh::lean_ctor_set(v___x_3263_, 7, v___x_3261_);
    crate::leanh::lean_ctor_set(v___x_3263_, 8, v___x_3261_);
    crate::leanh::lean_ctor_set(v___x_3263_, 9, v___x_3261_);
    return v___x_3263_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3264_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3265_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3265_, 0, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3265_, 1, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3265_, 2, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3265_, 3, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3265_, 4, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3265_, 5, v___x_3264_);
    return v___x_3265_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3267_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3266_);
    crate::leanh::lean_ctor_set(v___x_3267_, 1, v___x_3266_);
    crate::leanh::lean_ctor_set(v___x_3267_, 2, v___x_3266_);
    crate::leanh::lean_ctor_set(v___x_3267_, 3, v___x_3266_);
    crate::leanh::lean_ctor_set(v___x_3267_, 4, v___x_3266_);
    return v___x_3267_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3269_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4);
    v___x_3270_ = crate::leanh::lean_box(1);
    v___x_3271_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
    v___x_3273_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3273_, 0, v___x_3272_);
    crate::leanh::lean_ctor_set(v___x_3273_, 1, v___x_3271_);
    crate::leanh::lean_ctor_set(v___x_3273_, 2, v___x_3270_);
    crate::leanh::lean_ctor_set(v___x_3273_, 3, v___x_3269_);
    crate::leanh::lean_ctor_set(v___x_3273_, 4, v___x_3268_);
    return v___x_3273_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(
    mut v_name_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v_a_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u64 = 0;
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3278_ = lean_st_ref_get(v___y_3276_);
                v_env_3279_ = crate::leanh::lean_ctor_get(v___x_3278_, 0);
                crate::leanh::lean_inc_ref(v_env_3279_);
                crate::leanh::lean_dec(v___x_3278_);
                crate::leanh::lean_inc(v_name_3274_);
                v___x_3280_ =
                    l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(
                        v_env_3279_,
                        v_name_3274_,
                    );
                if v___x_3280_ == 0 {
                    crate::leanh::lean_dec(v_name_3274_);
                    v___x_3288_ = crate::leanh::lean_box((v___x_3280_) as usize);
                    v___x_3289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3289_, 0, v___x_3288_);
                    return v___x_3289_;
                } else {
                    v___x_3290_ = 0;
                    v___x_3291_ = 1;
                    v___x_3292_ = 0;
                    v___x_3293_ = 2;
                    v___x_3294_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 0 as u32, v___x_3290_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 1 as u32, v___x_3290_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 2 as u32, v___x_3290_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 3 as u32, v___x_3290_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 4 as u32, v___x_3290_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 5 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 6 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 7 as u32, v___x_3290_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 8 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 9 as u32, v___x_3291_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 10 as u32, v___x_3292_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 11 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 12 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 13 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 14 as u32, v___x_3293_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 15 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 16 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 17 as u32, v___x_3280_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3294_, 18 as u32, v___x_3280_);
                    v___x_3295_ =
                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3294_);
                    v___x_3296_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v___x_3296_, 0, v___x_3294_);
                    crate::leanh::lean_ctor_set_uint64(
                        v___x_3296_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3295_,
                    );
                    v___x_3297_ = crate::leanh::lean_box(1);
                    v___x_3298_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
                    v___x_3300_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
                    v___x_3301_ = crate::leanh::lean_box(0);
                    v___x_3302_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v___x_3302_, 0, v___x_3296_);
                    crate::leanh::lean_ctor_set(v___x_3302_, 1, v___x_3297_);
                    crate::leanh::lean_ctor_set(v___x_3302_, 2, v___x_3299_);
                    crate::leanh::lean_ctor_set(v___x_3302_, 3, v___x_3300_);
                    crate::leanh::lean_ctor_set(v___x_3302_, 4, v___x_3301_);
                    crate::leanh::lean_ctor_set(v___x_3302_, 5, v___x_3298_);
                    crate::leanh::lean_ctor_set(v___x_3302_, 6, v___x_3301_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3302_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v___x_3290_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3302_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v___x_3290_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3302_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v___x_3290_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3302_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                        v___x_3280_,
                    );
                    v___x_3303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
                    v___x_3304_ = lean_st_mk_ref(v___x_3303_);
                    v___x_3305_ = l_Lean_Name_getPrefix(v_name_3274_);
                    v___x_3306_ = l_Lean_Meta_getSparseCasesOnEq(
                        v___x_3305_,
                        v___x_3302_,
                        v___x_3304_,
                        v___y_3275_,
                        v___y_3276_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_3302_, 7);
                    if crate::leanh::lean_obj_tag(v___x_3306_) == 0 {
                        v_a_3307_ = crate::leanh::lean_ctor_get(v___x_3306_, 0);
                        crate::leanh::lean_inc(v_a_3307_);
                        crate::leanh::lean_dec_ref_known(v___x_3306_, 1);
                        v___x_3308_ = lean_st_ref_get(v___x_3304_);
                        crate::leanh::lean_dec(v___x_3304_);
                        crate::leanh::lean_dec(v___x_3308_);
                        v_a_3282_ = v_a_3307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3304_);
                        if crate::leanh::lean_obj_tag(v___x_3306_) == 0 {
                            v_a_3309_ = crate::leanh::lean_ctor_get(v___x_3306_, 0);
                            crate::leanh::lean_inc(v_a_3309_);
                            crate::leanh::lean_dec_ref_known(v___x_3306_, 1);
                            v_a_3282_ = v_a_3309_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_name_3274_);
                            v_a_3310_ = crate::leanh::lean_ctor_get(v___x_3306_, 0);
                            v_isSharedCheck_3317_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3306_)) as u8;
                            if v_isSharedCheck_3317_ == 0 {
                                v___x_3312_ = v___x_3306_;
                                v_isShared_3313_ = v_isSharedCheck_3317_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3310_);
                                crate::leanh::lean_dec(v___x_3306_);
                                v___x_3312_ = crate::leanh::lean_box(0);
                                v_isShared_3313_ = v_isSharedCheck_3317_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3283_ = lean_name_eq(v_name_3274_, v_a_3282_);
                crate::leanh::lean_dec(v_a_3282_);
                crate::leanh::lean_dec(v_name_3274_);
                if v___x_3283_ == 0 {
                    v___x_3284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
                    v___x_3285_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(v___x_3284_, v___y_3275_, v___y_3276_);
                    return v___x_3285_;
                } else {
                    v___x_3286_ = crate::leanh::lean_box((v___x_3280_) as usize);
                    v___x_3287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3287_, 0, v___x_3286_);
                    return v___x_3287_;
                }
            }
            2 => {
                if v_isShared_3313_ == 0 {
                    v___x_3315_ = v___x_3312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
                    v___x_3315_ = v_reuseFailAlloc_3316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(
    mut v_name_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3322_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(v_name_3318_, v___y_3319_, v___y_3320_);
    crate::leanh::lean_dec(v___y_3320_);
    crate::leanh::lean_dec_ref(v___y_3319_);
    return v_res_3322_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3325_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
    v___x_3326_ = l_Lean_registerReservedNameAction(v___f_3325_);
    return v___x_3326_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(
    mut v_a_3327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
    return v_res_3328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_SparseCasesOnEq(
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
pub unsafe fn initialize_Lean_Meta_Constructions_SparseCasesOnEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_HasNotBit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
}
