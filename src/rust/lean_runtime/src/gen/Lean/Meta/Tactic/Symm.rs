// Lean compiler output
// Module: Lean.Meta.Tactic.Symm
// Imports: Lean.Meta.Reduce Lean.Meta.Tactic.Replace Lean.Meta.DiscrTree.Main Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop;
use crate::r#gen::Init::Meta::Defs::lean_name_append_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_fvar___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr, l_Lean_mkAppN,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_toExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkExpectedTypeHint,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_FVarId_getUserName___redArg, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Main::{
    initialize_Lean_Meta_DiscrTree_Main, l_Lean_Meta_DiscrTree_getMatch___redArg,
    l_Lean_Meta_DiscrTree_mkPath, runtime_initialize_Lean_Meta_DiscrTree_Main,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::Reduce::{
    initialize_Lean_Meta_Reduce, l_Lean_Meta_reduce, runtime_initialize_Lean_Meta_Reduce,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_note;
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_replace,
    runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_MVarId_setTag___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__1_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__1_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 121, 109, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 121, 109, 109, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,10573563056024800507 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,5598089069436195276 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 68, m_data: [64, 91, 115, 121, 109, 109, 93, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 111, 110, 108, 121, 32, 97, 112, 112, 108, 105, 101, 115, 32, 116, 111, 32, 108, 101, 109, 109, 97, 115, 32, 112, 114, 111, 118, 105, 110, 103, 32, 120, 32, 226, 136, 188, 32, 121, 32, 226, 134, 146, 32, 121, 32, 226, 136, 188, 32, 120, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,16601512737180741990 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,2521957379553407087 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,10944073338883162370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,860630417816272470 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__11_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,16649640780980434551 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__11_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__11_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__12_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__12_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__12_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__13_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__11_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__12_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,15208305176460598470 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__13_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__13_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__14_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__14_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__14_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__15_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__13_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__14_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,278511632433040247 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__15_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__15_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__16_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__15_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__3_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,10880210200382116362 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__16_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__16_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__17_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__16_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,10718813657547686574 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__17_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__17_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__18_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__17_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,6774104536414203987 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__18_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__18_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__19_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__18_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__5_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__value) as *mut LeanObject,11012029812854649142 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__19_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__19_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__20_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__20_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__21_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__21_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__21_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__22_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__22_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__23_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__23_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__23_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__24_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__24_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__26_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 121, 109, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__26_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__26_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__27_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__26_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject,14245357698250389304 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__27_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__27_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__28_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__27_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__28_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__28_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__29_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 121, 109, 109, 101, 116, 114, 105, 99, 32, 114, 101, 108, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__29_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__29_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__30_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__30_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__31_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__31_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value: LeanStringObject<149> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 149, m_capacity: 149, m_length: 146, m_data: [84, 97, 103, 115, 32, 115, 121, 109, 109, 101, 116, 114, 121, 32, 108, 101, 109, 109, 97, 115, 32, 116, 111, 32, 98, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 96, 115, 121, 109, 109, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 65, 32, 115, 121, 109, 109, 101, 116, 114, 121, 32, 108, 101, 109, 109, 97, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 114, 32, 120, 32, 121, 32, 226, 134, 146, 32, 114, 32, 121, 32, 120, 96, 32, 119, 104, 101, 114, 101, 32, 96, 114, 96, 32, 105, 115, 32, 97, 110, 32, 97, 114, 98, 105, 116, 114, 97, 114, 121, 32, 114, 101, 108, 97, 116, 105, 111, 110, 46, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Expr_getSymmLems___closed__0_value: LeanStringObject<52> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        83, 121, 109, 109, 101, 116, 114, 121, 32, 108, 101, 109, 109, 97, 115, 32, 111, 110, 108,
        121, 32, 97, 112, 112, 108, 121, 32, 116, 111, 32, 98, 105, 110, 97, 114, 121, 32, 114,
        101, 108, 97, 116, 105, 111, 110, 115, 44, 32, 110, 111, 116, 0,
    ],
};
static mut l_Lean_Expr_getSymmLems___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_getSymmLems___closed__0_value) as *mut LeanObject;
static mut l_Lean_Expr_getSymmLems___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_getSymmLems___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__0_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [102, 97, 105, 108, 101, 100, 0],
};
static mut l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__0_value)
        as *mut LeanObject;
static mut l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_applySymm___closed__0_value: LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        78, 111, 32, 97, 112, 112, 108, 105, 99, 97, 98, 108, 101, 32, 115, 121, 109, 109, 101,
        116, 114, 121, 32, 108, 101, 109, 109, 97, 32, 102, 111, 117, 110, 100, 32, 102, 111, 114,
        0,
    ],
};
static mut l_Lean_Expr_applySymm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_applySymm___closed__0_value) as *mut LeanObject;
static mut l_Lean_Expr_applySymm___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_applySymm___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_applySymm___closed__2_value: LeanStringObject<74> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 74,
    m_capacity: 74,
    m_length: 73,
    m_data: [
        65, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 115, 121, 109, 109, 101, 116, 114, 121,
        32, 108, 101, 109, 109, 97, 115, 32, 99, 97, 110, 32, 98, 101, 32, 114, 101, 103, 105, 115,
        116, 101, 114, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 96, 91, 115,
        121, 109, 109, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Expr_applySymm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_applySymm___closed__2_value) as *mut LeanObject;
static mut l_Lean_Expr_applySymm___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_applySymm___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_applySymm___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_applySymm___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 115, 121, 109, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_(
    mut v_x_2947_: *mut LeanObject,
    mut v_a_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    v___x_2949_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2949_, 0, v_a_2948_);
    lean_inc_ref_n(v___x_2949_, 2);
    v___x_2950_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2950_, 0, v___x_2949_);
    lean_ctor_set(v___x_2950_, 1, v___x_2949_);
    lean_ctor_set(v___x_2950_, 2, v___x_2949_);
    return v___x_2950_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2____boxed(
    mut v_x_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2953_: *mut LeanObject = core::ptr::null_mut();
    v_res_2953_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_(v_x_2951_, v_a_2952_);
    lean_dec_ref(v_x_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_2954_: *mut LeanObject,
    mut v_vals_2955_: *mut LeanObject,
    mut v_i_2956_: *mut LeanObject,
    mut v_k_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2958_ = lean_array_get_size(v_keys_2954_);
                v___x_2959_ = lean_nat_dec_lt(v_i_2956_, v___x_2958_);
                if v___x_2959_ == 0 {
                    lean_dec(v_i_2956_);
                    v___x_2960_ = lean_box(0);
                    return v___x_2960_;
                } else {
                    v_k_x27_2961_ = lean_array_fget_borrowed(v_keys_2954_, v_i_2956_);
                    v___x_2962_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2957_, v_k_x27_2961_);
                    if v___x_2962_ == 0 {
                        v___x_2963_ = lean_unsigned_to_nat(1);
                        v___x_2964_ = lean_nat_add(v_i_2956_, v___x_2963_);
                        lean_dec(v_i_2956_);
                        v_i_2956_ = v___x_2964_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2966_ = lean_array_fget_borrowed(v_vals_2955_, v_i_2956_);
                        lean_dec(v_i_2956_);
                        lean_inc(v___x_2966_);
                        v___x_2967_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2967_, 0, v___x_2966_);
                        return v___x_2967_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_2968_: *mut LeanObject,
    mut v_vals_2969_: *mut LeanObject,
    mut v_i_2970_: *mut LeanObject,
    mut v_k_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2972_: *mut LeanObject = core::ptr::null_mut();
    v_res_2972_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2968_, v_vals_2969_, v_i_2970_, v_k_2971_);
    lean_dec(v_k_2971_);
    lean_dec_ref(v_vals_2969_);
    lean_dec_ref(v_keys_2968_);
    return v_res_2972_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2973_: usize = 0;
    let mut v___x_2974_: usize = 0;
    let mut v___x_2975_: usize = 0;
    v___x_2973_ = 5usize;
    v___x_2974_ = 1usize;
    v___x_2975_ = lean_usize_shift_left(v___x_2974_, v___x_2973_);
    return v___x_2975_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2976_: usize = 0;
    let mut v___x_2977_: usize = 0;
    let mut v___x_2978_: usize = 0;
    v___x_2976_ = 1usize;
    v___x_2977_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2978_ = lean_usize_sub(v___x_2977_, v___x_2976_);
    return v___x_2978_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_2979_: *mut LeanObject,
    mut v_x_2980_: usize,
    mut v_x_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: usize = 0;
    let mut v___x_2986_: usize = 0;
    let mut v_j_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: usize = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2979_) == 0 {
                    v_es_2982_ = lean_ctor_get(v_x_2979_, 0);
                    v___x_2983_ = lean_box(2);
                    v___x_2984_ = 5usize;
                    v___x_2985_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2986_ = lean_usize_land(v_x_2980_, v___x_2985_);
                    v_j_2987_ = lean_usize_to_nat(v___x_2986_);
                    v___x_2988_ = lean_array_get_borrowed(v___x_2983_, v_es_2982_, v_j_2987_);
                    lean_dec(v_j_2987_);
                    match lean_obj_tag(v___x_2988_) {
                        0 => {
                            v_key_2989_ = lean_ctor_get(v___x_2988_, 0);
                            v_val_2990_ = lean_ctor_get(v___x_2988_, 1);
                            v___x_2991_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2981_, v_key_2989_);
                            if v___x_2991_ == 0 {
                                v___x_2992_ = lean_box(0);
                                return v___x_2992_;
                            } else {
                                lean_inc(v_val_2990_);
                                v___x_2993_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2993_, 0, v_val_2990_);
                                return v___x_2993_;
                            }
                        }
                        1 => {
                            v_node_2994_ = lean_ctor_get(v___x_2988_, 0);
                            v___x_2995_ = lean_usize_shift_right(v_x_2980_, v___x_2984_);
                            v_x_2979_ = v_node_2994_;
                            v_x_2980_ = v___x_2995_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2997_ = lean_box(0);
                            return v___x_2997_;
                        }
                    }
                } else {
                    v_ks_2998_ = lean_ctor_get(v_x_2979_, 0);
                    v_vs_2999_ = lean_ctor_get(v_x_2979_, 1);
                    v___x_3000_ = lean_unsigned_to_nat(0);
                    v___x_3001_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2998_, v_vs_2999_, v___x_3000_, v_x_2981_);
                    return v___x_3001_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_3002_: *mut LeanObject,
    mut v_x_3003_: *mut LeanObject,
    mut v_x_3004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1591__boxed_3005_: usize = 0;
    let mut v_res_3006_: *mut LeanObject = core::ptr::null_mut();
    v_x_1591__boxed_3005_ = lean_unbox_usize(v_x_3003_);
    lean_dec(v_x_3003_);
    v_res_3006_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_3002_, v_x_1591__boxed_3005_, v_x_3004_);
    lean_dec(v_x_3004_);
    lean_dec_ref(v_x_3002_);
    return v_res_3006_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_3007_: *mut LeanObject,
    mut v_x_3008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3009_: u64 = 0;
    let mut v___x_3010_: usize = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    v___x_3009_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_3008_);
    v___x_3010_ = lean_uint64_to_usize(v___x_3009_);
    v___x_3011_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_3007_, v___x_3010_, v_x_3008_);
    return v___x_3011_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_3012_: *mut LeanObject,
    mut v_x_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3014_: *mut LeanObject = core::ptr::null_mut();
    v_res_3014_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_3012_, v_x_3013_);
    lean_dec(v_x_3013_);
    lean_dec_ref(v_x_3012_);
    return v_res_3014_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    v___x_3015_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
    return v___x_3015_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3(
    mut v_msg_3016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    v___x_3017_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0);
    v___x_3018_ = lean_panic_fn_borrowed(v___x_3017_, v_msg_3016_);
    return v___x_3018_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(
    mut v_a_3019_: *mut LeanObject,
    mut v_b_3020_: *mut LeanObject,
) -> u8 {
    let mut v_fst_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: u8 = 0;
    v_fst_3021_ = lean_ctor_get(v_a_3019_, 0);
    v_fst_3022_ = lean_ctor_get(v_b_3020_, 0);
    v___x_3023_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_3021_, v_fst_3022_);
    return v___x_3023_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(
    mut v_a_3024_: *mut LeanObject,
    mut v_b_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3026_: u8 = 0;
    let mut v_r_3027_: *mut LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_a_3024_, v_b_3025_);
    lean_dec_ref(v_b_3025_);
    lean_dec_ref(v_a_3024_);
    v_r_3027_ = lean_box((v_res_3026_) as usize);
    return v_r_3027_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(
    mut v_x_3028_: *mut LeanObject,
    mut v_keys_3029_: *mut LeanObject,
    mut v_v_3030_: *mut LeanObject,
    mut v_k_3031_: *mut LeanObject,
    mut v_x_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    v___x_3033_ = lean_unsigned_to_nat(1);
    v___x_3034_ = lean_nat_add(v_x_3028_, v___x_3033_);
    v_c_3035_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        lean_box(0),
        v_keys_3029_,
        v_v_3030_,
        v___x_3034_,
    );
    lean_dec(v___x_3034_);
    v___x_3036_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3036_, 0, v_k_3031_);
    lean_ctor_set(v___x_3036_, 1, v_c_3035_);
    return v___x_3036_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(
    mut v_x_3037_: *mut LeanObject,
    mut v_keys_3038_: *mut LeanObject,
    mut v_v_3039_: *mut LeanObject,
    mut v_k_3040_: *mut LeanObject,
    mut v_x_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_3037_, v_keys_3038_, v_v_3039_, v_k_3040_, v_x_3041_);
    lean_dec_ref(v_keys_3038_);
    lean_dec(v_x_3037_);
    return v_res_3042_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(
    mut v_vs_3043_: *mut LeanObject,
    mut v_v_3044_: *mut LeanObject,
    mut v_i_3045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: u8 = 0;
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3046_ = lean_array_get_size(v_vs_3043_);
                v___x_3047_ = lean_nat_dec_lt(v_i_3045_, v___x_3046_);
                if v___x_3047_ == 0 {
                    lean_dec(v_i_3045_);
                    v___x_3048_ = lean_array_push(v_vs_3043_, v_v_3044_);
                    return v___x_3048_;
                } else {
                    v___x_3049_ = lean_array_fget_borrowed(v_vs_3043_, v_i_3045_);
                    v___x_3050_ = lean_name_eq(v_v_3044_, v___x_3049_);
                    if v___x_3050_ == 0 {
                        v___x_3051_ = lean_unsigned_to_nat(1);
                        v___x_3052_ = lean_nat_add(v_i_3045_, v___x_3051_);
                        lean_dec(v_i_3045_);
                        v_i_3045_ = v___x_3052_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3054_ = lean_array_fset(v_vs_3043_, v_i_3045_, v_v_3044_);
                        lean_dec(v_i_3045_);
                        return v___x_3054_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__5(
    mut v_vs_3055_: *mut LeanObject,
    mut v_v_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    v___x_3057_ = lean_unsigned_to_nat(0);
    v___x_3058_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(v_vs_3055_, v_v_3056_, v___x_3057_);
    return v___x_3058_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_x_3063_: *mut LeanObject,
    mut v_keys_3064_: *mut LeanObject,
    mut v_v_3065_: *mut LeanObject,
    mut v_k_3066_: *mut LeanObject,
    mut v_as_3067_: *mut LeanObject,
    mut v_k_3068_: *mut LeanObject,
    mut v_x_3069_: *mut LeanObject,
    mut v_x_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_midVal_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    let mut v_snd_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut v_unused_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3071_ = lean_nat_add(v_x_3069_, v_x_3070_);
                v___x_3072_ = lean_unsigned_to_nat(1);
                v_mid_3073_ = lean_nat_shiftr(v___x_3071_, v___x_3072_);
                lean_dec(v___x_3071_);
                v_midVal_3074_ = lean_array_fget(v_as_3067_, v_mid_3073_);
                v___x_3075_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_midVal_3074_, v_k_3068_);
                if v___x_3075_ == 0 {
                    lean_dec(v_x_3070_);
                    v___x_3076_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_3068_, v_midVal_3074_);
                    if v___x_3076_ == 0 {
                        lean_dec(v_x_3069_);
                        v___x_3077_ = lean_array_get_size(v_as_3067_);
                        v___x_3078_ = lean_nat_dec_lt(v_mid_3073_, v___x_3077_);
                        if v___x_3078_ == 0 {
                            lean_dec(v_midVal_3074_);
                            lean_dec(v_mid_3073_);
                            lean_dec(v_k_3066_);
                            lean_dec(v_v_3065_);
                            return v_as_3067_;
                        } else {
                            v_snd_3079_ = lean_ctor_get(v_midVal_3074_, 1);
                            v_isSharedCheck_3091_ = (!lean_is_exclusive(v_midVal_3074_)) as u8;
                            if v_isSharedCheck_3091_ == 0 {
                                v_unused_3092_ = lean_ctor_get(v_midVal_3074_, 0);
                                lean_dec(v_unused_3092_);
                                v___x_3081_ = v_midVal_3074_;
                                v_isShared_3082_ = v_isSharedCheck_3091_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_3079_);
                                lean_dec(v_midVal_3074_);
                                v___x_3081_ = lean_box(0);
                                v_isShared_3082_ = v_isSharedCheck_3091_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_midVal_3074_);
                        v_x_3070_ = v_mid_3073_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_midVal_3074_);
                    v___x_3094_ = lean_nat_dec_eq(v_mid_3073_, v_x_3069_);
                    if v___x_3094_ == 0 {
                        lean_dec(v_x_3069_);
                        v_x_3069_ = v_mid_3073_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mid_3073_);
                        lean_dec(v_x_3070_);
                        v___x_3096_ = lean_nat_add(v_x_3063_, v___x_3072_);
                        v_c_3097_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_3064_, v_v_3065_, v___x_3096_);
                        lean_dec(v___x_3096_);
                        v___x_3098_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3098_, 0, v_k_3066_);
                        lean_ctor_set(v___x_3098_, 1, v_c_3097_);
                        v___x_3099_ = lean_nat_add(v_x_3069_, v___x_3072_);
                        lean_dec(v_x_3069_);
                        v_j_3100_ = lean_array_get_size(v_as_3067_);
                        v_as_3101_ = lean_array_push(v_as_3067_, v___x_3098_);
                        v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            lean_box(0),
                            v___x_3099_,
                            v_as_3101_,
                            v_j_3100_,
                        );
                        lean_dec(v___x_3099_);
                        return v___x_3102_;
                    }
                }
            }
            1 => {
                v___x_3083_ = lean_box(0);
                v_xs_x27_3084_ = lean_array_fset(v_as_3067_, v_mid_3073_, v___x_3083_);
                v___x_3085_ = lean_nat_add(v_x_3063_, v___x_3072_);
                v_c_3086_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2(v_keys_3064_, v_v_3065_, v___x_3085_, v_snd_3079_);
                lean_dec(v___x_3085_);
                if v_isShared_3082_ == 0 {
                    lean_ctor_set(v___x_3081_, 1, v_c_3086_);
                    lean_ctor_set(v___x_3081_, 0, v_k_3066_);
                    v___x_3088_ = v___x_3081_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_k_3066_);
                    lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_c_3086_);
                    v___x_3088_ = v_reuseFailAlloc_3090_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3089_ = lean_array_fset(v_xs_x27_3084_, v_mid_3073_, v___x_3088_);
                lean_dec(v_mid_3073_);
                return v___x_3089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6(
    mut v_x_3103_: *mut LeanObject,
    mut v_keys_3104_: *mut LeanObject,
    mut v_v_3105_: *mut LeanObject,
    mut v_k_3106_: *mut LeanObject,
    mut v_as_3107_: *mut LeanObject,
    mut v_k_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    v___x_3109_ = lean_array_get_size(v_as_3107_);
    v___x_3110_ = lean_unsigned_to_nat(0);
    v___x_3111_ = lean_nat_dec_eq(v___x_3109_, v___x_3110_);
    if v___x_3111_ == 0 {
        let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3113_: u8 = 0;
        v___x_3112_ = lean_array_fget_borrowed(v_as_3107_, v___x_3110_);
        v___x_3113_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_3108_, v___x_3112_);
        if v___x_3113_ == 0 {
            let mut v___x_3114_: u8 = 0;
            v___x_3114_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_3112_, v_k_3108_);
            if v___x_3114_ == 0 {
                let mut v___x_3115_: u8 = 0;
                v___x_3115_ = lean_nat_dec_lt(v___x_3110_, v___x_3109_);
                if v___x_3115_ == 0 {
                    lean_dec(v_k_3106_);
                    lean_dec(v_v_3105_);
                    return v_as_3107_;
                } else {
                    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_3117_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v___x_3112_);
                    v___x_3116_ = lean_box(0);
                    v_xs_x27_3117_ = lean_array_fset(v_as_3107_, v___x_3110_, v___x_3116_);
                    v___x_3118_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_3103_, v_keys_3104_, v_v_3105_, v_k_3106_, v___x_3112_);
                    v___x_3119_ = lean_array_fset(v_xs_x27_3117_, v___x_3110_, v___x_3118_);
                    return v___x_3119_;
                }
            } else {
                let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3123_: u8 = 0;
                v___x_3120_ = lean_unsigned_to_nat(1);
                v___x_3121_ = lean_nat_sub(v___x_3109_, v___x_3120_);
                v___x_3122_ = lean_array_fget_borrowed(v_as_3107_, v___x_3121_);
                v___x_3123_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_3122_, v_k_3108_);
                if v___x_3123_ == 0 {
                    let mut v___x_3124_: u8 = 0;
                    v___x_3124_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_3108_, v___x_3122_);
                    if v___x_3124_ == 0 {
                        let mut v___x_3125_: u8 = 0;
                        v___x_3125_ = lean_nat_dec_lt(v___x_3121_, v___x_3109_);
                        if v___x_3125_ == 0 {
                            lean_dec(v___x_3121_);
                            lean_dec(v_k_3106_);
                            lean_dec(v_v_3105_);
                            return v_as_3107_;
                        } else {
                            let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_xs_x27_3127_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
                            lean_inc(v___x_3122_);
                            v___x_3126_ = lean_box(0);
                            v_xs_x27_3127_ = lean_array_fset(v_as_3107_, v___x_3121_, v___x_3126_);
                            v___x_3128_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_3103_, v_keys_3104_, v_v_3105_, v_k_3106_, v___x_3122_);
                            v___x_3129_ = lean_array_fset(v_xs_x27_3127_, v___x_3121_, v___x_3128_);
                            lean_dec(v___x_3121_);
                            return v___x_3129_;
                        }
                    } else {
                        let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
                        v___x_3130_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_3103_, v_keys_3104_, v_v_3105_, v_k_3106_, v_as_3107_, v_k_3108_, v___x_3110_, v___x_3121_);
                        return v___x_3130_;
                    }
                } else {
                    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_3121_);
                    v___x_3131_ = lean_box(0);
                    v___x_3132_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_3103_, v_keys_3104_, v_v_3105_, v_k_3106_, v___x_3131_);
                    v___x_3133_ = lean_array_push(v_as_3107_, v___x_3132_);
                    return v___x_3133_;
                }
            }
        } else {
            let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
            let mut v_as_3136_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
            v___x_3134_ = lean_box(0);
            v___x_3135_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_3103_, v_keys_3104_, v_v_3105_, v_k_3106_, v___x_3134_);
            v_as_3136_ = lean_array_push(v_as_3107_, v___x_3135_);
            v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                lean_box(0),
                v___x_3110_,
                v_as_3136_,
                v___x_3109_,
            );
            return v___x_3137_;
        }
    } else {
        let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
        v___x_3138_ = lean_box(0);
        v___x_3139_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_3103_, v_keys_3104_, v_v_3105_, v_k_3106_, v___x_3138_);
        v___x_3140_ = lean_array_push(v_as_3107_, v___x_3139_);
        return v___x_3140_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2(
    mut v_keys_3141_: *mut LeanObject,
    mut v_v_3142_: *mut LeanObject,
    mut v_x_3143_: *mut LeanObject,
    mut v_x_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_3145_ = lean_ctor_get(v_x_3144_, 0);
                v_children_3146_ = lean_ctor_get(v_x_3144_, 1);
                v_isSharedCheck_3163_ = (!lean_is_exclusive(v_x_3144_)) as u8;
                if v_isSharedCheck_3163_ == 0 {
                    v___x_3148_ = v_x_3144_;
                    v_isShared_3149_ = v_isSharedCheck_3163_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_3146_);
                    lean_inc(v_vs_3145_);
                    lean_dec(v_x_3144_);
                    v___x_3148_ = lean_box(0);
                    v_isShared_3149_ = v_isSharedCheck_3163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3150_ = lean_array_get_size(v_keys_3141_);
                v___x_3151_ = lean_nat_dec_lt(v_x_3143_, v___x_3150_);
                if v___x_3151_ == 0 {
                    v___x_3152_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_vs_3145_, v_v_3142_);
                    if v_isShared_3149_ == 0 {
                        lean_ctor_set(v___x_3148_, 0, v___x_3152_);
                        v___x_3154_ = v___x_3148_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
                        lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_children_3146_);
                        v___x_3154_ = v_reuseFailAlloc_3155_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_3156_ = lean_array_fget_borrowed(v_keys_3141_, v_x_3143_);
                    v___x_3157_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___closed__1;
                    lean_inc_n(v_k_3156_, 2);
                    v___x_3158_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3158_, 0, v_k_3156_);
                    lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                    v_c_3159_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_3143_, v_keys_3141_, v_v_3142_, v_k_3156_, v_children_3146_, v___x_3158_);
                    lean_dec_ref_known(v___x_3158_, 2);
                    if v_isShared_3149_ == 0 {
                        lean_ctor_set(v___x_3148_, 1, v_c_3159_);
                        v___x_3161_ = v___x_3148_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_vs_3145_);
                        lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_c_3159_);
                        v___x_3161_ = v_reuseFailAlloc_3162_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3154_;
            }
            3 => {
                return v___x_3161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(
    mut v_x_3164_: *mut LeanObject,
    mut v_keys_3165_: *mut LeanObject,
    mut v_v_3166_: *mut LeanObject,
    mut v_k_3167_: *mut LeanObject,
    mut v_x_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3169_ = lean_ctor_get(v_x_3168_, 1);
                v_isSharedCheck_3179_ = (!lean_is_exclusive(v_x_3168_)) as u8;
                if v_isSharedCheck_3179_ == 0 {
                    v_unused_3180_ = lean_ctor_get(v_x_3168_, 0);
                    lean_dec(v_unused_3180_);
                    v___x_3171_ = v_x_3168_;
                    v_isShared_3172_ = v_isSharedCheck_3179_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3169_);
                    lean_dec(v_x_3168_);
                    v___x_3171_ = lean_box(0);
                    v_isShared_3172_ = v_isSharedCheck_3179_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3173_ = lean_unsigned_to_nat(1);
                v___x_3174_ = lean_nat_add(v_x_3164_, v___x_3173_);
                v_c_3175_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2(v_keys_3165_, v_v_3166_, v___x_3174_, v_snd_3169_);
                lean_dec(v___x_3174_);
                if v_isShared_3172_ == 0 {
                    lean_ctor_set(v___x_3171_, 1, v_c_3175_);
                    lean_ctor_set(v___x_3171_, 0, v_k_3167_);
                    v___x_3177_ = v___x_3171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_k_3167_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_c_3175_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(
    mut v_x_3181_: *mut LeanObject,
    mut v_keys_3182_: *mut LeanObject,
    mut v_v_3183_: *mut LeanObject,
    mut v_k_3184_: *mut LeanObject,
    mut v_x_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3186_: *mut LeanObject = core::ptr::null_mut();
    v_res_3186_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_3181_, v_keys_3182_, v_v_3183_, v_k_3184_, v_x_3185_);
    lean_dec_ref(v_keys_3182_);
    lean_dec(v_x_3181_);
    return v_res_3186_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2___boxed(
    mut v_keys_3187_: *mut LeanObject,
    mut v_v_3188_: *mut LeanObject,
    mut v_x_3189_: *mut LeanObject,
    mut v_x_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3191_: *mut LeanObject = core::ptr::null_mut();
    v_res_3191_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2(v_keys_3187_, v_v_3188_, v_x_3189_, v_x_3190_);
    lean_dec(v_x_3189_);
    lean_dec_ref(v_keys_3187_);
    return v_res_3191_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_x_3192_: *mut LeanObject,
    mut v_keys_3193_: *mut LeanObject,
    mut v_v_3194_: *mut LeanObject,
    mut v_k_3195_: *mut LeanObject,
    mut v_as_3196_: *mut LeanObject,
    mut v_k_3197_: *mut LeanObject,
    mut v_x_3198_: *mut LeanObject,
    mut v_x_3199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3200_: *mut LeanObject = core::ptr::null_mut();
    v_res_3200_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_3192_, v_keys_3193_, v_v_3194_, v_k_3195_, v_as_3196_, v_k_3197_, v_x_3198_, v_x_3199_);
    lean_dec_ref(v_k_3197_);
    lean_dec_ref(v_keys_3193_);
    lean_dec(v_x_3192_);
    return v_res_3200_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(
    mut v_x_3201_: *mut LeanObject,
    mut v_keys_3202_: *mut LeanObject,
    mut v_v_3203_: *mut LeanObject,
    mut v_k_3204_: *mut LeanObject,
    mut v_as_3205_: *mut LeanObject,
    mut v_k_3206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3207_: *mut LeanObject = core::ptr::null_mut();
    v_res_3207_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_3201_, v_keys_3202_, v_v_3203_, v_k_3204_, v_as_3205_, v_k_3206_);
    lean_dec_ref(v_k_3206_);
    lean_dec_ref(v_keys_3202_);
    lean_dec(v_x_3201_);
    return v_res_3207_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_x_3208_: *mut LeanObject,
    mut v_x_3209_: *mut LeanObject,
    mut v_x_3210_: *mut LeanObject,
    mut v_x_3211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3212_ = lean_ctor_get(v_x_3208_, 0);
                v_vs_3213_ = lean_ctor_get(v_x_3208_, 1);
                v_isSharedCheck_3237_ = (!lean_is_exclusive(v_x_3208_)) as u8;
                if v_isSharedCheck_3237_ == 0 {
                    v___x_3215_ = v_x_3208_;
                    v_isShared_3216_ = v_isSharedCheck_3237_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3213_);
                    lean_inc(v_ks_3212_);
                    lean_dec(v_x_3208_);
                    v___x_3215_ = lean_box(0);
                    v_isShared_3216_ = v_isSharedCheck_3237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3217_ = lean_array_get_size(v_ks_3212_);
                v___x_3218_ = lean_nat_dec_lt(v_x_3209_, v___x_3217_);
                if v___x_3218_ == 0 {
                    lean_dec(v_x_3209_);
                    v___x_3219_ = lean_array_push(v_ks_3212_, v_x_3210_);
                    v___x_3220_ = lean_array_push(v_vs_3213_, v_x_3211_);
                    if v_isShared_3216_ == 0 {
                        lean_ctor_set(v___x_3215_, 1, v___x_3220_);
                        lean_ctor_set(v___x_3215_, 0, v___x_3219_);
                        v___x_3222_ = v___x_3215_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3219_);
                        lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___x_3220_);
                        v___x_3222_ = v_reuseFailAlloc_3223_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3224_ = lean_array_fget_borrowed(v_ks_3212_, v_x_3209_);
                    v___x_3225_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3210_, v_k_x27_3224_);
                    if v___x_3225_ == 0 {
                        if v_isShared_3216_ == 0 {
                            v___x_3227_ = v___x_3215_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_ks_3212_);
                            lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_vs_3213_);
                            v___x_3227_ = v_reuseFailAlloc_3231_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3232_ = lean_array_fset(v_ks_3212_, v_x_3209_, v_x_3210_);
                        v___x_3233_ = lean_array_fset(v_vs_3213_, v_x_3209_, v_x_3211_);
                        lean_dec(v_x_3209_);
                        if v_isShared_3216_ == 0 {
                            lean_ctor_set(v___x_3215_, 1, v___x_3233_);
                            lean_ctor_set(v___x_3215_, 0, v___x_3232_);
                            v___x_3235_ = v___x_3215_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3232_);
                            lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3233_);
                            v___x_3235_ = v_reuseFailAlloc_3236_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3222_;
            }
            3 => {
                v___x_3228_ = lean_unsigned_to_nat(1);
                v___x_3229_ = lean_nat_add(v_x_3209_, v___x_3228_);
                lean_dec(v_x_3209_);
                v_x_3208_ = v___x_3227_;
                v_x_3209_ = v___x_3229_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_n_3238_: *mut LeanObject,
    mut v_k_3239_: *mut LeanObject,
    mut v_v_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___x_3241_ = lean_unsigned_to_nat(0);
    v___x_3242_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_3238_, v___x_3241_, v_k_3239_, v_v_3240_);
    return v___x_3242_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3243_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_3244_: *mut LeanObject,
    mut v_x_3245_: usize,
    mut v_x_3246_: usize,
    mut v_x_3247_: *mut LeanObject,
    mut v_x_3248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3253_: usize = 0;
    let mut v_j_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u8 = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v_v_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_node_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3285_: usize = 0;
    let mut v___x_3286_: usize = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_unused_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: u8 = 0;
    let mut v_ks_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: u8 = 0;
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v_reuseFailAlloc_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3244_) == 0 {
                    v_es_3249_ = lean_ctor_get(v_x_3244_, 0);
                    v___x_3250_ = 5usize;
                    v___x_3251_ = 1usize;
                    v___x_3252_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3253_ = lean_usize_land(v_x_3245_, v___x_3252_);
                    v_j_3254_ = lean_usize_to_nat(v___x_3253_);
                    v___x_3255_ = lean_array_get_size(v_es_3249_);
                    v___x_3256_ = lean_nat_dec_lt(v_j_3254_, v___x_3255_);
                    if v___x_3256_ == 0 {
                        lean_dec(v_j_3254_);
                        lean_dec(v_x_3248_);
                        lean_dec(v_x_3247_);
                        return v_x_3244_;
                    } else {
                        lean_inc_ref(v_es_3249_);
                        v_isSharedCheck_3293_ = (!lean_is_exclusive(v_x_3244_)) as u8;
                        if v_isSharedCheck_3293_ == 0 {
                            v_unused_3294_ = lean_ctor_get(v_x_3244_, 0);
                            lean_dec(v_unused_3294_);
                            v___x_3258_ = v_x_3244_;
                            v_isShared_3259_ = v_isSharedCheck_3293_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3244_);
                            v___x_3258_ = lean_box(0);
                            v_isShared_3259_ = v_isSharedCheck_3293_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3295_ = lean_ctor_get(v_x_3244_, 0);
                    v_vs_3296_ = lean_ctor_get(v_x_3244_, 1);
                    v_isSharedCheck_3316_ = (!lean_is_exclusive(v_x_3244_)) as u8;
                    if v_isSharedCheck_3316_ == 0 {
                        v___x_3298_ = v_x_3244_;
                        v_isShared_3299_ = v_isSharedCheck_3316_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3296_);
                        lean_inc(v_ks_3295_);
                        lean_dec(v_x_3244_);
                        v___x_3298_ = lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3316_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3260_ = lean_array_fget(v_es_3249_, v_j_3254_);
                v___x_3261_ = lean_box(0);
                v_xs_x27_3262_ = lean_array_fset(v_es_3249_, v_j_3254_, v___x_3261_);
                match lean_obj_tag(v_v_3260_) {
                    0 => {
                        v_key_3269_ = lean_ctor_get(v_v_3260_, 0);
                        v_val_3270_ = lean_ctor_get(v_v_3260_, 1);
                        v_isSharedCheck_3280_ = (!lean_is_exclusive(v_v_3260_)) as u8;
                        if v_isSharedCheck_3280_ == 0 {
                            v___x_3272_ = v_v_3260_;
                            v_isShared_3273_ = v_isSharedCheck_3280_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3270_);
                            lean_inc(v_key_3269_);
                            lean_dec(v_v_3260_);
                            v___x_3272_ = lean_box(0);
                            v_isShared_3273_ = v_isSharedCheck_3280_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3281_ = lean_ctor_get(v_v_3260_, 0);
                        v_isSharedCheck_3291_ = (!lean_is_exclusive(v_v_3260_)) as u8;
                        if v_isSharedCheck_3291_ == 0 {
                            v___x_3283_ = v_v_3260_;
                            v_isShared_3284_ = v_isSharedCheck_3291_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3281_);
                            lean_dec(v_v_3260_);
                            v___x_3283_ = lean_box(0);
                            v_isShared_3284_ = v_isSharedCheck_3291_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3292_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3292_, 0, v_x_3247_);
                        lean_ctor_set(v___x_3292_, 1, v_x_3248_);
                        v___y_3264_ = v___x_3292_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3265_ = lean_array_fset(v_xs_x27_3262_, v_j_3254_, v___y_3264_);
                lean_dec(v_j_3254_);
                if v_isShared_3259_ == 0 {
                    lean_ctor_set(v___x_3258_, 0, v___x_3265_);
                    v___x_3267_ = v___x_3258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
                    v___x_3267_ = v_reuseFailAlloc_3268_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3267_;
            }
            4 => {
                v___x_3274_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3247_, v_key_3269_);
                if v___x_3274_ == 0 {
                    lean_del_object(v___x_3272_);
                    v___x_3275_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3269_,
                        v_val_3270_,
                        v_x_3247_,
                        v_x_3248_,
                    );
                    v___x_3276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                    v___y_3264_ = v___x_3276_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3270_);
                    lean_dec(v_key_3269_);
                    if v_isShared_3273_ == 0 {
                        lean_ctor_set(v___x_3272_, 1, v_x_3248_);
                        lean_ctor_set(v___x_3272_, 0, v_x_3247_);
                        v___x_3278_ = v___x_3272_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_x_3247_);
                        lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_x_3248_);
                        v___x_3278_ = v_reuseFailAlloc_3279_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3264_ = v___x_3278_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3285_ = lean_usize_shift_right(v_x_3245_, v___x_3250_);
                v___x_3286_ = lean_usize_add(v_x_3246_, v___x_3251_);
                v___x_3287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_node_3281_, v___x_3285_, v___x_3286_, v_x_3247_, v_x_3248_);
                if v_isShared_3284_ == 0 {
                    lean_ctor_set(v___x_3283_, 0, v___x_3287_);
                    v___x_3289_ = v___x_3283_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3264_ = v___x_3289_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3299_ == 0 {
                    v___x_3301_ = v___x_3298_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_ks_3295_);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_vs_3296_);
                    v___x_3301_ = v_reuseFailAlloc_3315_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3302_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(v___x_3301_, v_x_3247_, v_x_3248_);
                v___x_3310_ = 7usize;
                v___x_3311_ = lean_usize_dec_le(v___x_3310_, v_x_3246_);
                if v___x_3311_ == 0 {
                    v___x_3312_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3302_);
                    v___x_3313_ = lean_unsigned_to_nat(4);
                    v___x_3314_ = lean_nat_dec_lt(v___x_3312_, v___x_3313_);
                    lean_dec(v___x_3312_);
                    v___y_3304_ = v___x_3314_;
                    state = 10;
                    continue;
                } else {
                    v___y_3304_ = v___x_3311_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3304_ == 0 {
                    v_ks_3305_ = lean_ctor_get(v_newNode_3302_, 0);
                    lean_inc_ref(v_ks_3305_);
                    v_vs_3306_ = lean_ctor_get(v_newNode_3302_, 1);
                    lean_inc_ref(v_vs_3306_);
                    lean_dec_ref(v_newNode_3302_);
                    v___x_3307_ = lean_unsigned_to_nat(0);
                    v___x_3308_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0);
                    v___x_3309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_x_3246_, v_ks_3305_, v_vs_3306_, v___x_3307_, v___x_3308_);
                    lean_dec_ref(v_vs_3306_);
                    lean_dec_ref(v_ks_3305_);
                    return v___x_3309_;
                } else {
                    return v_newNode_3302_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_depth_3317_: usize,
    mut v_keys_3318_: *mut LeanObject,
    mut v_vals_3319_: *mut LeanObject,
    mut v_i_3320_: *mut LeanObject,
    mut v_entries_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: u8 = 0;
    let mut v_k_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u64 = 0;
    let mut v_h_3327_: usize = 0;
    let mut v___x_3328_: usize = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: usize = 0;
    let mut v_h_3333_: usize = 0;
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3322_ = lean_array_get_size(v_keys_3318_);
                v___x_3323_ = lean_nat_dec_lt(v_i_3320_, v___x_3322_);
                if v___x_3323_ == 0 {
                    lean_dec(v_i_3320_);
                    return v_entries_3321_;
                } else {
                    v_k_3324_ = lean_array_fget_borrowed(v_keys_3318_, v_i_3320_);
                    v_v_3325_ = lean_array_fget_borrowed(v_vals_3319_, v_i_3320_);
                    v___x_3326_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_3324_);
                    v_h_3327_ = lean_uint64_to_usize(v___x_3326_);
                    v___x_3328_ = 5usize;
                    v___x_3329_ = lean_unsigned_to_nat(1);
                    v___x_3330_ = 1usize;
                    v___x_3331_ = lean_usize_sub(v_depth_3317_, v___x_3330_);
                    v___x_3332_ = lean_usize_mul(v___x_3328_, v___x_3331_);
                    v_h_3333_ = lean_usize_shift_right(v_h_3327_, v___x_3332_);
                    v___x_3334_ = lean_nat_add(v_i_3320_, v___x_3329_);
                    lean_dec(v_i_3320_);
                    lean_inc(v_v_3325_);
                    lean_inc(v_k_3324_);
                    v___x_3335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_entries_3321_, v_h_3333_, v_depth_3317_, v_k_3324_, v_v_3325_);
                    v_i_3320_ = v___x_3334_;
                    v_entries_3321_ = v___x_3335_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_depth_3337_: *mut LeanObject,
    mut v_keys_3338_: *mut LeanObject,
    mut v_vals_3339_: *mut LeanObject,
    mut v_i_3340_: *mut LeanObject,
    mut v_entries_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3342_: usize = 0;
    let mut v_res_3343_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3342_ = lean_unbox_usize(v_depth_3337_);
    lean_dec(v_depth_3337_);
    v_res_3343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_3342_, v_keys_3338_, v_vals_3339_, v_i_3340_, v_entries_3341_);
    lean_dec_ref(v_vals_3339_);
    lean_dec_ref(v_keys_3338_);
    return v_res_3343_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_3344_: *mut LeanObject,
    mut v_x_3345_: *mut LeanObject,
    mut v_x_3346_: *mut LeanObject,
    mut v_x_3347_: *mut LeanObject,
    mut v_x_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1985__boxed_3349_: usize = 0;
    let mut v_x_1986__boxed_3350_: usize = 0;
    let mut v_res_3351_: *mut LeanObject = core::ptr::null_mut();
    v_x_1985__boxed_3349_ = lean_unbox_usize(v_x_3345_);
    lean_dec(v_x_3345_);
    v_x_1986__boxed_3350_ = lean_unbox_usize(v_x_3346_);
    lean_dec(v_x_3346_);
    v_res_3351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_3344_, v_x_1985__boxed_3349_, v_x_1986__boxed_3350_, v_x_3347_, v_x_3348_);
    return v_res_3351_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_3352_: *mut LeanObject,
    mut v_x_3353_: *mut LeanObject,
    mut v_x_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3355_: u64 = 0;
    let mut v___x_3356_: usize = 0;
    let mut v___x_3357_: usize = 0;
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    v___x_3355_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_3353_);
    v___x_3356_ = lean_uint64_to_usize(v___x_3355_);
    v___x_3357_ = 1usize;
    v___x_3358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_3352_, v___x_3356_, v___x_3357_, v_x_3353_, v_x_3354_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__2;
    v___x_3363_ = lean_unsigned_to_nat(23);
    v___x_3364_ = lean_unsigned_to_nat(166);
    v___x_3365_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__1;
    v___x_3366_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__0;
    v___x_3367_ = l_mkPanicMessageWithDecl(
        v___x_3366_,
        v___x_3365_,
        v___x_3364_,
        v___x_3363_,
        v___x_3362_,
    );
    return v___x_3367_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0(
    mut v_d_3368_: *mut LeanObject,
    mut v_keys_3369_: *mut LeanObject,
    mut v_v_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u8 = 0;
    v___x_3371_ = lean_array_get_size(v_keys_3369_);
    v___x_3372_ = lean_unsigned_to_nat(0);
    v___x_3373_ = lean_nat_dec_eq(v___x_3371_, v___x_3372_);
    if v___x_3373_ == 0 {
        let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
        v___x_3374_ = lean_box(0);
        v_k_3375_ = lean_array_get_borrowed(v___x_3374_, v_keys_3369_, v___x_3372_);
        v___x_3376_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0___redArg(v_d_3368_, v_k_3375_);
        if lean_obj_tag(v___x_3376_) == 0 {
            let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_3378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
            v___x_3377_ = lean_unsigned_to_nat(1);
            v_c_3378_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                lean_box(0),
                v_keys_3369_,
                v_v_3370_,
                v___x_3377_,
            );
            lean_inc(v_k_3375_);
            v___x_3379_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_3368_, v_k_3375_, v_c_3378_);
            return v___x_3379_;
        } else {
            let mut v_val_3380_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_3382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
            v_val_3380_ = lean_ctor_get(v___x_3376_, 0);
            lean_inc(v_val_3380_);
            lean_dec_ref_known(v___x_3376_, 1);
            v___x_3381_ = lean_unsigned_to_nat(1);
            v_c_3382_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2(v_keys_3369_, v_v_3370_, v___x_3381_, v_val_3380_);
            lean_inc(v_k_3375_);
            v___x_3383_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_3368_, v_k_3375_, v_c_3382_);
            return v___x_3383_;
        }
    } else {
        let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_v_3370_);
        lean_dec_ref(v_d_3368_);
        v___x_3384_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___closed__3);
        v___x_3385_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3(v___x_3384_);
        return v___x_3385_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0___boxed(
    mut v_d_3386_: *mut LeanObject,
    mut v_keys_3387_: *mut LeanObject,
    mut v_v_3388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3389_: *mut LeanObject = core::ptr::null_mut();
    v_res_3389_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0(v_d_3386_, v_keys_3387_, v_v_3388_);
    lean_dec_ref(v_keys_3387_);
    return v_res_3389_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_(
    mut v_dt_3390_: *mut LeanObject,
    mut v_x_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3392_ = lean_ctor_get(v_x_3391_, 0);
    lean_inc(v_fst_3392_);
    v_snd_3393_ = lean_ctor_get(v_x_3391_, 1);
    lean_inc(v_snd_3393_);
    lean_dec_ref(v_x_3391_);
    v___x_3394_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0(v_dt_3390_, v_snd_3393_, v_fst_3392_);
    lean_dec(v_snd_3393_);
    return v___x_3394_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_(
    mut v___y_3395_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3395_);
    return v___y_3395_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2____boxed(
    mut v___y_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3397_: *mut LeanObject = core::ptr::null_mut();
    v_res_3397_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_(v___y_3396_);
    lean_dec_ref(v___y_3396_);
    return v_res_3397_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3410_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__8_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_);
    v___x_3412_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3412_, 0, v___x_3411_);
    return v___x_3412_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    v___f_3413_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__0_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_;
    v___f_3414_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__2_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_;
    v___x_3415_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__9_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_);
    v___f_3416_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__1_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_;
    v___x_3417_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_;
    v___x_3418_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3418_, 0, v___x_3417_);
    lean_ctor_set(v___x_3418_, 1, v___f_3416_);
    lean_ctor_set(v___x_3418_, 2, v___x_3415_);
    lean_ctor_set(v___x_3418_, 3, v___f_3414_);
    lean_ctor_set(v___x_3418_, 4, v___f_3413_);
    return v___x_3418_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    v___x_3420_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__10_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_);
    v___x_3421_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3420_);
    return v___x_3421_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2____boxed(
    mut v_a_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3423_: *mut LeanObject = core::ptr::null_mut();
    v_res_3423_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_();
    return v_res_3423_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_3424_: *mut LeanObject,
    mut v_x_3425_: *mut LeanObject,
    mut v_x_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_3425_, v_x_3426_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_3428_: *mut LeanObject,
    mut v_x_3429_: *mut LeanObject,
    mut v_x_3430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3431_: *mut LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_3428_, v_x_3429_, v_x_3430_);
    lean_dec(v_x_3430_);
    lean_dec_ref(v_x_3429_);
    return v_res_3431_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_3432_: *mut LeanObject,
    mut v_x_3433_: *mut LeanObject,
    mut v_x_3434_: *mut LeanObject,
    mut v_x_3435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    v___x_3436_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_3433_, v_x_3434_, v_x_3435_);
    return v___x_3436_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_3437_: *mut LeanObject,
    mut v_x_3438_: *mut LeanObject,
    mut v_x_3439_: usize,
    mut v_x_3440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_3438_, v_x_3439_, v_x_3440_);
    return v___x_3441_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3442_: *mut LeanObject,
    mut v_x_3443_: *mut LeanObject,
    mut v_x_3444_: *mut LeanObject,
    mut v_x_3445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2303__boxed_3446_: usize = 0;
    let mut v_res_3447_: *mut LeanObject = core::ptr::null_mut();
    v_x_2303__boxed_3446_ = lean_unbox_usize(v_x_3444_);
    lean_dec(v_x_3444_);
    v_res_3447_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_3442_, v_x_3443_, v_x_2303__boxed_3446_, v_x_3445_);
    lean_dec(v_x_3445_);
    lean_dec_ref(v_x_3443_);
    return v_res_3447_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_3448_: *mut LeanObject,
    mut v_x_3449_: *mut LeanObject,
    mut v_x_3450_: usize,
    mut v_x_3451_: usize,
    mut v_x_3452_: *mut LeanObject,
    mut v_x_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    v___x_3454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_3449_, v_x_3450_, v_x_3451_, v_x_3452_, v_x_3453_);
    return v___x_3454_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3455_: *mut LeanObject,
    mut v_x_3456_: *mut LeanObject,
    mut v_x_3457_: *mut LeanObject,
    mut v_x_3458_: *mut LeanObject,
    mut v_x_3459_: *mut LeanObject,
    mut v_x_3460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2314__boxed_3461_: usize = 0;
    let mut v_x_2315__boxed_3462_: usize = 0;
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_x_2314__boxed_3461_ = lean_unbox_usize(v_x_3457_);
    lean_dec(v_x_3457_);
    v_x_2315__boxed_3462_ = lean_unbox_usize(v_x_3458_);
    lean_dec(v_x_3458_);
    v_res_3463_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_3455_, v_x_3456_, v_x_2314__boxed_3461_, v_x_2315__boxed_3462_, v_x_3459_, v_x_3460_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3464_: *mut LeanObject,
    mut v_keys_3465_: *mut LeanObject,
    mut v_vals_3466_: *mut LeanObject,
    mut v_heq_3467_: *mut LeanObject,
    mut v_i_3468_: *mut LeanObject,
    mut v_k_3469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    v___x_3470_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3465_, v_vals_3466_, v_i_3468_, v_k_3469_);
    return v___x_3470_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3471_: *mut LeanObject,
    mut v_keys_3472_: *mut LeanObject,
    mut v_vals_3473_: *mut LeanObject,
    mut v_heq_3474_: *mut LeanObject,
    mut v_i_3475_: *mut LeanObject,
    mut v_k_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3477_: *mut LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3471_, v_keys_3472_, v_vals_3473_, v_heq_3474_, v_i_3475_, v_k_3476_);
    lean_dec(v_k_3476_);
    lean_dec_ref(v_vals_3473_);
    lean_dec_ref(v_keys_3472_);
    return v_res_3477_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_3478_: *mut LeanObject,
    mut v_n_3479_: *mut LeanObject,
    mut v_k_3480_: *mut LeanObject,
    mut v_v_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    v___x_3482_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(v_n_3479_, v_k_3480_, v_v_3481_);
    return v___x_3482_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_3483_: *mut LeanObject,
    mut v_depth_3484_: usize,
    mut v_keys_3485_: *mut LeanObject,
    mut v_vals_3486_: *mut LeanObject,
    mut v_heq_3487_: *mut LeanObject,
    mut v_i_3488_: *mut LeanObject,
    mut v_entries_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    v___x_3490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_depth_3484_, v_keys_3485_, v_vals_3486_, v_i_3488_, v_entries_3489_);
    return v___x_3490_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_3491_: *mut LeanObject,
    mut v_depth_3492_: *mut LeanObject,
    mut v_keys_3493_: *mut LeanObject,
    mut v_vals_3494_: *mut LeanObject,
    mut v_heq_3495_: *mut LeanObject,
    mut v_i_3496_: *mut LeanObject,
    mut v_entries_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3498_: usize = 0;
    let mut v_res_3499_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3498_ = lean_unbox_usize(v_depth_3492_);
    lean_dec(v_depth_3492_);
    v_res_3499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_3491_, v_depth_boxed_3498_, v_keys_3493_, v_vals_3494_, v_heq_3495_, v_i_3496_, v_entries_3497_);
    lean_dec_ref(v_vals_3494_);
    lean_dec_ref(v_keys_3493_);
    return v_res_3499_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(
    mut v_x_3500_: *mut LeanObject,
    mut v_keys_3501_: *mut LeanObject,
    mut v_v_3502_: *mut LeanObject,
    mut v_k_3503_: *mut LeanObject,
    mut v_as_3504_: *mut LeanObject,
    mut v_k_3505_: *mut LeanObject,
    mut v_x_3506_: *mut LeanObject,
    mut v_x_3507_: *mut LeanObject,
    mut v_x_3508_: *mut LeanObject,
    mut v_x_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    v___x_3510_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_3500_, v_keys_3501_, v_v_3502_, v_k_3503_, v_as_3504_, v_k_3505_, v_x_3506_, v_x_3507_);
    return v___x_3510_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_x_3511_: *mut LeanObject,
    mut v_keys_3512_: *mut LeanObject,
    mut v_v_3513_: *mut LeanObject,
    mut v_k_3514_: *mut LeanObject,
    mut v_as_3515_: *mut LeanObject,
    mut v_k_3516_: *mut LeanObject,
    mut v_x_3517_: *mut LeanObject,
    mut v_x_3518_: *mut LeanObject,
    mut v_x_3519_: *mut LeanObject,
    mut v_x_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3521_: *mut LeanObject = core::ptr::null_mut();
    v_res_3521_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(v_x_3511_, v_keys_3512_, v_v_3513_, v_k_3514_, v_as_3515_, v_k_3516_, v_x_3517_, v_x_3518_, v_x_3519_, v_x_3520_);
    lean_dec_ref(v_k_3516_);
    lean_dec_ref(v_keys_3512_);
    lean_dec(v_x_3511_);
    return v_res_3521_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_3522_: *mut LeanObject,
    mut v_x_3523_: *mut LeanObject,
    mut v_x_3524_: *mut LeanObject,
    mut v_x_3525_: *mut LeanObject,
    mut v_x_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    v___x_3527_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_3523_, v_x_3524_, v_x_3525_, v_x_3526_);
    return v___x_3527_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    v___x_3528_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3528_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    v___x_3529_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__0);
    v___x_3530_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3530_, 0, v___x_3529_);
    return v___x_3530_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    v___x_3531_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1);
    v___x_3532_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3532_, 0, v___x_3531_);
    lean_ctor_set(v___x_3532_, 1, v___x_3531_);
    return v___x_3532_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    v___x_3533_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__1);
    v___x_3534_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3534_, 0, v___x_3533_);
    lean_ctor_set(v___x_3534_, 1, v___x_3533_);
    lean_ctor_set(v___x_3534_, 2, v___x_3533_);
    lean_ctor_set(v___x_3534_, 3, v___x_3533_);
    lean_ctor_set(v___x_3534_, 4, v___x_3533_);
    lean_ctor_set(v___x_3534_, 5, v___x_3533_);
    return v___x_3534_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg(
    mut v_ext_3535_: *mut LeanObject,
    mut v_b_3536_: *mut LeanObject,
    mut v_kind_3537_: u8,
    mut v___y_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3575_: u8 = 0;
    let mut v_unused_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_unused_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_3542_ = lean_ctor_get(v___y_3539_, 6);
                v___x_3543_ = lean_st_ref_take(v___y_3540_);
                v_env_3544_ = lean_ctor_get(v___x_3543_, 0);
                v_nextMacroScope_3545_ = lean_ctor_get(v___x_3543_, 1);
                v_ngen_3546_ = lean_ctor_get(v___x_3543_, 2);
                v_auxDeclNGen_3547_ = lean_ctor_get(v___x_3543_, 3);
                v_traceState_3548_ = lean_ctor_get(v___x_3543_, 4);
                v_messages_3549_ = lean_ctor_get(v___x_3543_, 6);
                v_infoState_3550_ = lean_ctor_get(v___x_3543_, 7);
                v_snapshotTasks_3551_ = lean_ctor_get(v___x_3543_, 8);
                v_isSharedCheck_3578_ = (!lean_is_exclusive(v___x_3543_)) as u8;
                if v_isSharedCheck_3578_ == 0 {
                    v_unused_3579_ = lean_ctor_get(v___x_3543_, 5);
                    lean_dec(v_unused_3579_);
                    v___x_3553_ = v___x_3543_;
                    v_isShared_3554_ = v_isSharedCheck_3578_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3551_);
                    lean_inc(v_infoState_3550_);
                    lean_inc(v_messages_3549_);
                    lean_inc(v_traceState_3548_);
                    lean_inc(v_auxDeclNGen_3547_);
                    lean_inc(v_ngen_3546_);
                    lean_inc(v_nextMacroScope_3545_);
                    lean_inc(v_env_3544_);
                    lean_dec(v___x_3543_);
                    v___x_3553_ = lean_box(0);
                    v_isShared_3554_ = v_isSharedCheck_3578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_3542_);
                v___x_3555_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_3544_,
                    v_ext_3535_,
                    v_b_3536_,
                    v_kind_3537_,
                    v_currNamespace_3542_,
                );
                v___x_3556_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__2);
                if v_isShared_3554_ == 0 {
                    lean_ctor_set(v___x_3553_, 5, v___x_3556_);
                    lean_ctor_set(v___x_3553_, 0, v___x_3555_);
                    v___x_3558_ = v___x_3553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_nextMacroScope_3545_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_ngen_3546_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_auxDeclNGen_3547_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_traceState_3548_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 5, v___x_3556_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 6, v_messages_3549_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 7, v_infoState_3550_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 8, v_snapshotTasks_3551_);
                    v___x_3558_ = v_reuseFailAlloc_3577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3559_ = lean_st_ref_set(v___y_3540_, v___x_3558_);
                v___x_3560_ = lean_st_ref_take(v___y_3538_);
                v_mctx_3561_ = lean_ctor_get(v___x_3560_, 0);
                v_zetaDeltaFVarIds_3562_ = lean_ctor_get(v___x_3560_, 2);
                v_postponed_3563_ = lean_ctor_get(v___x_3560_, 3);
                v_diag_3564_ = lean_ctor_get(v___x_3560_, 4);
                v_isSharedCheck_3575_ = (!lean_is_exclusive(v___x_3560_)) as u8;
                if v_isSharedCheck_3575_ == 0 {
                    v_unused_3576_ = lean_ctor_get(v___x_3560_, 1);
                    lean_dec(v_unused_3576_);
                    v___x_3566_ = v___x_3560_;
                    v_isShared_3567_ = v_isSharedCheck_3575_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_3564_);
                    lean_inc(v_postponed_3563_);
                    lean_inc(v_zetaDeltaFVarIds_3562_);
                    lean_inc(v_mctx_3561_);
                    lean_dec(v___x_3560_);
                    v___x_3566_ = lean_box(0);
                    v_isShared_3567_ = v_isSharedCheck_3575_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3568_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___closed__3);
                if v_isShared_3567_ == 0 {
                    lean_ctor_set(v___x_3566_, 1, v___x_3568_);
                    v___x_3570_ = v___x_3566_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_mctx_3561_);
                    lean_ctor_set(v_reuseFailAlloc_3574_, 1, v___x_3568_);
                    lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_zetaDeltaFVarIds_3562_);
                    lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_postponed_3563_);
                    lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_diag_3564_);
                    v___x_3570_ = v_reuseFailAlloc_3574_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3571_ = lean_st_ref_set(v___y_3538_, v___x_3570_);
                v___x_3572_ = lean_box(0);
                v___x_3573_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3573_, 0, v___x_3572_);
                return v___x_3573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_ext_3580_: *mut LeanObject,
    mut v_b_3581_: *mut LeanObject,
    mut v_kind_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3587_: u8 = 0;
    let mut v_res_3588_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3587_ = (lean_unbox(v_kind_3582_) as u8);
    v_res_3588_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg(v_ext_3580_, v_b_3581_, v_kind_boxed_3587_, v___y_3583_, v___y_3584_, v___y_3585_);
    lean_dec(v___y_3585_);
    lean_dec_ref(v___y_3584_);
    lean_dec(v___y_3583_);
    return v_res_3588_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2(
    mut v_00_u03b1_3589_: *mut LeanObject,
    mut v_00_u03b2_3590_: *mut LeanObject,
    mut v_00_u03c3_3591_: *mut LeanObject,
    mut v_ext_3592_: *mut LeanObject,
    mut v_b_3593_: *mut LeanObject,
    mut v_kind_3594_: u8,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    v___x_3600_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg(v_ext_3592_, v_b_3593_, v_kind_3594_, v___y_3596_, v___y_3597_, v___y_3598_);
    return v___x_3600_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b1_3601_: *mut LeanObject,
    mut v_00_u03b2_3602_: *mut LeanObject,
    mut v_00_u03c3_3603_: *mut LeanObject,
    mut v_ext_3604_: *mut LeanObject,
    mut v_b_3605_: *mut LeanObject,
    mut v_kind_3606_: *mut LeanObject,
    mut v___y_3607_: *mut LeanObject,
    mut v___y_3608_: *mut LeanObject,
    mut v___y_3609_: *mut LeanObject,
    mut v___y_3610_: *mut LeanObject,
    mut v___y_3611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3612_: u8 = 0;
    let mut v_res_3613_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3612_ = (lean_unbox(v_kind_3606_) as u8);
    v_res_3613_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2(v_00_u03b1_3601_, v_00_u03b2_3602_, v_00_u03c3_3603_, v_ext_3604_, v_b_3605_, v_kind_boxed_3612_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
    lean_dec(v___y_3610_);
    lean_dec_ref(v___y_3609_);
    lean_dec(v___y_3608_);
    lean_dec_ref(v___y_3607_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1_spec__2(
    mut v_msgData_3614_: *mut LeanObject,
    mut v___y_3615_: *mut LeanObject,
    mut v___y_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    v___x_3620_ = lean_st_ref_get(v___y_3618_);
    v_env_3621_ = lean_ctor_get(v___x_3620_, 0);
    lean_inc_ref(v_env_3621_);
    lean_dec(v___x_3620_);
    v___x_3622_ = lean_st_ref_get(v___y_3616_);
    v_mctx_3623_ = lean_ctor_get(v___x_3622_, 0);
    lean_inc_ref(v_mctx_3623_);
    lean_dec(v___x_3622_);
    v_lctx_3624_ = lean_ctor_get(v___y_3615_, 2);
    v_options_3625_ = lean_ctor_get(v___y_3617_, 2);
    lean_inc_ref(v_options_3625_);
    lean_inc_ref(v_lctx_3624_);
    v___x_3626_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3626_, 0, v_env_3621_);
    lean_ctor_set(v___x_3626_, 1, v_mctx_3623_);
    lean_ctor_set(v___x_3626_, 2, v_lctx_3624_);
    lean_ctor_set(v___x_3626_, 3, v_options_3625_);
    v___x_3627_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3627_, 0, v___x_3626_);
    lean_ctor_set(v___x_3627_, 1, v_msgData_3614_);
    v___x_3628_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3628_, 0, v___x_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_msgData_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3635_: *mut LeanObject = core::ptr::null_mut();
    v_res_3635_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1_spec__2(v_msgData_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
    lean_dec(v___y_3633_);
    lean_dec_ref(v___y_3632_);
    lean_dec(v___y_3631_);
    lean_dec_ref(v___y_3630_);
    return v_res_3635_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(
    mut v_msg_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3642_ = lean_ctor_get(v___y_3639_, 5);
                v___x_3643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1_spec__2(v_msg_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
                v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
                v_isSharedCheck_3652_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                if v_isSharedCheck_3652_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    v_isShared_3647_ = v_isSharedCheck_3652_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3644_);
                    lean_dec(v___x_3643_);
                    v___x_3646_ = lean_box(0);
                    v_isShared_3647_ = v_isSharedCheck_3652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3642_);
                v___x_3648_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3648_, 0, v_ref_3642_);
                lean_ctor_set(v___x_3648_, 1, v_a_3644_);
                if v_isShared_3647_ == 0 {
                    lean_ctor_set_tag(v___x_3646_, 1);
                    lean_ctor_set(v___x_3646_, 0, v___x_3648_);
                    v___x_3650_ = v___x_3646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
                    v___x_3650_ = v_reuseFailAlloc_3651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_msg_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
    mut v___y_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3659_: *mut LeanObject = core::ptr::null_mut();
    v_res_3659_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v_msg_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
    lean_dec(v___y_3657_);
    lean_dec_ref(v___y_3656_);
    lean_dec(v___y_3655_);
    lean_dec_ref(v___y_3654_);
    return v_res_3659_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    v___x_3660_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3660_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    v___x_3661_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_3662_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3662_, 0, v___x_3661_);
    return v___x_3662_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    v___x_3663_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_3664_ = lean_unsigned_to_nat(0);
    v___x_3665_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3665_, 0, v___x_3664_);
    lean_ctor_set(v___x_3665_, 1, v___x_3664_);
    lean_ctor_set(v___x_3665_, 2, v___x_3664_);
    lean_ctor_set(v___x_3665_, 3, v___x_3664_);
    lean_ctor_set(v___x_3665_, 4, v___x_3663_);
    lean_ctor_set(v___x_3665_, 5, v___x_3663_);
    lean_ctor_set(v___x_3665_, 6, v___x_3663_);
    lean_ctor_set(v___x_3665_, 7, v___x_3663_);
    lean_ctor_set(v___x_3665_, 8, v___x_3663_);
    lean_ctor_set(v___x_3665_, 9, v___x_3663_);
    return v___x_3665_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    v___x_3666_ = lean_unsigned_to_nat(32);
    v___x_3667_ = lean_mk_empty_array_with_capacity(v___x_3666_);
    v___x_3668_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3668_, 0, v___x_3667_);
    return v___x_3668_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3669_: usize = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    v___x_3669_ = 5usize;
    v___x_3670_ = lean_unsigned_to_nat(0);
    v___x_3671_ = lean_unsigned_to_nat(32);
    v___x_3672_ = lean_mk_empty_array_with_capacity(v___x_3671_);
    v___x_3673_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_3674_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3674_, 0, v___x_3673_);
    lean_ctor_set(v___x_3674_, 1, v___x_3672_);
    lean_ctor_set(v___x_3674_, 2, v___x_3670_);
    lean_ctor_set(v___x_3674_, 3, v___x_3670_);
    lean_ctor_set_usize(v___x_3674_, 4, v___x_3669_);
    return v___x_3674_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    v___x_3675_ = lean_box(1);
    v___x_3676_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_3677_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_3678_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3678_, 0, v___x_3677_);
    lean_ctor_set(v___x_3678_, 1, v___x_3676_);
    lean_ctor_set(v___x_3678_, 2, v___x_3675_);
    return v___x_3678_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    v___x_3680_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_3681_ = l_Lean_stringToMessageData(v___x_3680_);
    return v___x_3681_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    v___x_3683_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_3684_ = l_Lean_stringToMessageData(v___x_3683_);
    return v___x_3684_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3686_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_3687_ = l_Lean_stringToMessageData(v___x_3686_);
    return v___x_3687_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    v___x_3689_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
    return v___x_3690_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
    return v___x_3693_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    v___x_3695_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
    return v___x_3696_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    v___x_3698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
    return v___x_3699_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg(
    mut v_msg_3700_: *mut LeanObject,
    mut v_declHint_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: u8 = 0;
    let mut v_isExporting_3707_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3704_ = lean_st_ref_get(v___y_3702_);
                v_env_3705_ = lean_ctor_get(v___x_3704_, 0);
                lean_inc_ref(v_env_3705_);
                lean_dec(v___x_3704_);
                v___x_3706_ = l_Lean_Name_isAnonymous(v_declHint_3701_);
                if v___x_3706_ == 0 {
                    v_isExporting_3707_ = lean_ctor_get_uint8(
                        v_env_3705_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3707_ == 0 {
                        lean_dec_ref(v_env_3705_);
                        lean_dec(v_declHint_3701_);
                        v___x_3708_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3708_, 0, v_msg_3700_);
                        return v___x_3708_;
                    } else {
                        lean_inc_ref(v_env_3705_);
                        v___x_3709_ = l_Lean_Environment_setExporting(v_env_3705_, v___x_3706_);
                        lean_inc(v_declHint_3701_);
                        lean_inc_ref(v___x_3709_);
                        v___x_3710_ = l_Lean_Environment_contains(
                            v___x_3709_,
                            v_declHint_3701_,
                            v_isExporting_3707_,
                        );
                        if v___x_3710_ == 0 {
                            lean_dec_ref(v___x_3709_);
                            lean_dec_ref(v_env_3705_);
                            lean_dec(v_declHint_3701_);
                            v___x_3711_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3711_, 0, v_msg_3700_);
                            return v___x_3711_;
                        } else {
                            v___x_3712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_3713_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_3714_ = l_Lean_Options_empty;
                            v___x_3715_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3715_, 0, v___x_3709_);
                            lean_ctor_set(v___x_3715_, 1, v___x_3712_);
                            lean_ctor_set(v___x_3715_, 2, v___x_3713_);
                            lean_ctor_set(v___x_3715_, 3, v___x_3714_);
                            lean_inc(v_declHint_3701_);
                            v___x_3716_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3701_, v___x_3706_);
                            v_c_3717_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3717_, 0, v___x_3715_);
                            lean_ctor_set(v_c_3717_, 1, v___x_3716_);
                            v___x_3718_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3705_,
                                v_declHint_3701_,
                            );
                            if lean_obj_tag(v___x_3718_) == 0 {
                                lean_dec_ref(v_env_3705_);
                                lean_dec(v_declHint_3701_);
                                v___x_3719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_3720_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3720_, 0, v___x_3719_);
                                lean_ctor_set(v___x_3720_, 1, v_c_3717_);
                                v___x_3721_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_3722_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3722_, 0, v___x_3720_);
                                lean_ctor_set(v___x_3722_, 1, v___x_3721_);
                                v___x_3723_ = l_Lean_MessageData_note(v___x_3722_);
                                v___x_3724_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3724_, 0, v_msg_3700_);
                                lean_ctor_set(v___x_3724_, 1, v___x_3723_);
                                v___x_3725_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3725_, 0, v___x_3724_);
                                return v___x_3725_;
                            } else {
                                v_val_3726_ = lean_ctor_get(v___x_3718_, 0);
                                v_isSharedCheck_3761_ = (!lean_is_exclusive(v___x_3718_)) as u8;
                                if v_isSharedCheck_3761_ == 0 {
                                    v___x_3728_ = v___x_3718_;
                                    v_isShared_3729_ = v_isSharedCheck_3761_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3726_);
                                    lean_dec(v___x_3718_);
                                    v___x_3728_ = lean_box(0);
                                    v_isShared_3729_ = v_isSharedCheck_3761_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3705_);
                    lean_dec(v_declHint_3701_);
                    v___x_3762_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3762_, 0, v_msg_3700_);
                    return v___x_3762_;
                }
            }
            1 => {
                v___x_3730_ = lean_box(0);
                v___x_3731_ = l_Lean_Environment_header(v_env_3705_);
                lean_dec_ref(v_env_3705_);
                v___x_3732_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3731_);
                v_mod_3733_ = lean_array_get(v___x_3730_, v___x_3732_, v_val_3726_);
                lean_dec(v_val_3726_);
                lean_dec_ref(v___x_3732_);
                v___x_3734_ = l_Lean_isPrivateName(v_declHint_3701_);
                lean_dec(v_declHint_3701_);
                if v___x_3734_ == 0 {
                    v___x_3735_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_3736_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3736_, 0, v___x_3735_);
                    lean_ctor_set(v___x_3736_, 1, v_c_3717_);
                    v___x_3737_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_3738_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3738_, 0, v___x_3736_);
                    lean_ctor_set(v___x_3738_, 1, v___x_3737_);
                    v___x_3739_ = l_Lean_MessageData_ofName(v_mod_3733_);
                    v___x_3740_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3740_, 0, v___x_3738_);
                    lean_ctor_set(v___x_3740_, 1, v___x_3739_);
                    v___x_3741_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_3742_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3742_, 0, v___x_3740_);
                    lean_ctor_set(v___x_3742_, 1, v___x_3741_);
                    v___x_3743_ = l_Lean_MessageData_note(v___x_3742_);
                    v___x_3744_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3744_, 0, v_msg_3700_);
                    lean_ctor_set(v___x_3744_, 1, v___x_3743_);
                    if v_isShared_3729_ == 0 {
                        lean_ctor_set_tag(v___x_3728_, 0);
                        lean_ctor_set(v___x_3728_, 0, v___x_3744_);
                        v___x_3746_ = v___x_3728_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
                        v___x_3746_ = v_reuseFailAlloc_3747_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3748_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_3749_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3749_, 0, v___x_3748_);
                    lean_ctor_set(v___x_3749_, 1, v_c_3717_);
                    v___x_3750_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_3751_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3751_, 0, v___x_3749_);
                    lean_ctor_set(v___x_3751_, 1, v___x_3750_);
                    v___x_3752_ = l_Lean_MessageData_ofName(v_mod_3733_);
                    v___x_3753_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3753_, 0, v___x_3751_);
                    lean_ctor_set(v___x_3753_, 1, v___x_3752_);
                    v___x_3754_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_3755_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3755_, 0, v___x_3753_);
                    lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                    v___x_3756_ = l_Lean_MessageData_note(v___x_3755_);
                    v___x_3757_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3757_, 0, v_msg_3700_);
                    lean_ctor_set(v___x_3757_, 1, v___x_3756_);
                    if v_isShared_3729_ == 0 {
                        lean_ctor_set_tag(v___x_3728_, 0);
                        lean_ctor_set(v___x_3728_, 0, v___x_3757_);
                        v___x_3759_ = v___x_3728_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
                        v___x_3759_ = v_reuseFailAlloc_3760_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3746_;
            }
            3 => {
                return v___x_3759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_3763_: *mut LeanObject,
    mut v_declHint_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3767_: *mut LeanObject = core::ptr::null_mut();
    v_res_3767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg(v_msg_3763_, v_declHint_3764_, v___y_3765_);
    lean_dec(v___y_3765_);
    return v_res_3767_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8(
    mut v_msg_3768_: *mut LeanObject,
    mut v_declHint_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
    mut v___y_3771_: *mut LeanObject,
    mut v___y_3772_: *mut LeanObject,
    mut v___y_3773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3775_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg(v_msg_3768_, v_declHint_3769_, v___y_3773_);
                v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
                v_isSharedCheck_3785_ = (!lean_is_exclusive(v___x_3775_)) as u8;
                if v_isSharedCheck_3785_ == 0 {
                    v___x_3778_ = v___x_3775_;
                    v_isShared_3779_ = v_isSharedCheck_3785_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3776_);
                    lean_dec(v___x_3775_);
                    v___x_3778_ = lean_box(0);
                    v_isShared_3779_ = v_isSharedCheck_3785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3780_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3781_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3781_, 0, v___x_3780_);
                lean_ctor_set(v___x_3781_, 1, v_a_3776_);
                if v_isShared_3779_ == 0 {
                    lean_ctor_set(v___x_3778_, 0, v___x_3781_);
                    v___x_3783_ = v___x_3778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
                    v___x_3783_ = v_reuseFailAlloc_3784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8___boxed(
    mut v_msg_3786_: *mut LeanObject,
    mut v_declHint_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3793_: *mut LeanObject = core::ptr::null_mut();
    v_res_3793_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8(v_msg_3786_, v_declHint_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
    lean_dec(v___y_3791_);
    lean_dec_ref(v___y_3790_);
    lean_dec(v___y_3789_);
    lean_dec_ref(v___y_3788_);
    return v_res_3793_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9___redArg(
    mut v_ref_3794_: *mut LeanObject,
    mut v_msg_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3813_: u8 = 0;
    let mut v_cancelTk_x3f_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3815_: u8 = 0;
    let mut v_inheritedTraceOptions_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3801_ = lean_ctor_get(v___y_3798_, 0);
    v_fileMap_3802_ = lean_ctor_get(v___y_3798_, 1);
    v_options_3803_ = lean_ctor_get(v___y_3798_, 2);
    v_currRecDepth_3804_ = lean_ctor_get(v___y_3798_, 3);
    v_maxRecDepth_3805_ = lean_ctor_get(v___y_3798_, 4);
    v_ref_3806_ = lean_ctor_get(v___y_3798_, 5);
    v_currNamespace_3807_ = lean_ctor_get(v___y_3798_, 6);
    v_openDecls_3808_ = lean_ctor_get(v___y_3798_, 7);
    v_initHeartbeats_3809_ = lean_ctor_get(v___y_3798_, 8);
    v_maxHeartbeats_3810_ = lean_ctor_get(v___y_3798_, 9);
    v_quotContext_3811_ = lean_ctor_get(v___y_3798_, 10);
    v_currMacroScope_3812_ = lean_ctor_get(v___y_3798_, 11);
    v_diag_3813_ = lean_ctor_get_uint8(
        v___y_3798_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3814_ = lean_ctor_get(v___y_3798_, 12);
    v_suppressElabErrors_3815_ = lean_ctor_get_uint8(
        v___y_3798_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3816_ = lean_ctor_get(v___y_3798_, 13);
    v_ref_3817_ = l_Lean_replaceRef(v_ref_3794_, v_ref_3806_);
    lean_inc_ref(v_inheritedTraceOptions_3816_);
    lean_inc(v_cancelTk_x3f_3814_);
    lean_inc(v_currMacroScope_3812_);
    lean_inc(v_quotContext_3811_);
    lean_inc(v_maxHeartbeats_3810_);
    lean_inc(v_initHeartbeats_3809_);
    lean_inc(v_openDecls_3808_);
    lean_inc(v_currNamespace_3807_);
    lean_inc(v_maxRecDepth_3805_);
    lean_inc(v_currRecDepth_3804_);
    lean_inc_ref(v_options_3803_);
    lean_inc_ref(v_fileMap_3802_);
    lean_inc_ref(v_fileName_3801_);
    v___x_3818_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3818_, 0, v_fileName_3801_);
    lean_ctor_set(v___x_3818_, 1, v_fileMap_3802_);
    lean_ctor_set(v___x_3818_, 2, v_options_3803_);
    lean_ctor_set(v___x_3818_, 3, v_currRecDepth_3804_);
    lean_ctor_set(v___x_3818_, 4, v_maxRecDepth_3805_);
    lean_ctor_set(v___x_3818_, 5, v_ref_3817_);
    lean_ctor_set(v___x_3818_, 6, v_currNamespace_3807_);
    lean_ctor_set(v___x_3818_, 7, v_openDecls_3808_);
    lean_ctor_set(v___x_3818_, 8, v_initHeartbeats_3809_);
    lean_ctor_set(v___x_3818_, 9, v_maxHeartbeats_3810_);
    lean_ctor_set(v___x_3818_, 10, v_quotContext_3811_);
    lean_ctor_set(v___x_3818_, 11, v_currMacroScope_3812_);
    lean_ctor_set(v___x_3818_, 12, v_cancelTk_x3f_3814_);
    lean_ctor_set(v___x_3818_, 13, v_inheritedTraceOptions_3816_);
    lean_ctor_set_uint8(
        v___x_3818_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3813_,
    );
    lean_ctor_set_uint8(
        v___x_3818_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3815_,
    );
    v___x_3819_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v_msg_3795_, v___y_3796_, v___y_3797_, v___x_3818_, v___y_3799_);
    lean_dec_ref_known(v___x_3818_, 14);
    return v___x_3819_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9___redArg___boxed(
    mut v_ref_3820_: *mut LeanObject,
    mut v_msg_3821_: *mut LeanObject,
    mut v___y_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3827_: *mut LeanObject = core::ptr::null_mut();
    v_res_3827_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9___redArg(v_ref_3820_, v_msg_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
    lean_dec(v___y_3825_);
    lean_dec_ref(v___y_3824_);
    lean_dec(v___y_3823_);
    lean_dec_ref(v___y_3822_);
    lean_dec(v_ref_3820_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(
    mut v_ref_3828_: *mut LeanObject,
    mut v_msg_3829_: *mut LeanObject,
    mut v_declHint_3830_: *mut LeanObject,
    mut v___y_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8(v_msg_3829_, v_declHint_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
    v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
    lean_inc(v_a_3837_);
    lean_dec_ref(v___x_3836_);
    v___x_3838_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9___redArg(v_ref_3828_, v_a_3837_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
    return v___x_3838_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(
    mut v_ref_3839_: *mut LeanObject,
    mut v_msg_3840_: *mut LeanObject,
    mut v_declHint_3841_: *mut LeanObject,
    mut v___y_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
    mut v___y_3845_: *mut LeanObject,
    mut v___y_3846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3847_: *mut LeanObject = core::ptr::null_mut();
    v_res_3847_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3839_, v_msg_3840_, v_declHint_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
    lean_dec(v___y_3845_);
    lean_dec_ref(v___y_3844_);
    lean_dec(v___y_3843_);
    lean_dec_ref(v___y_3842_);
    lean_dec(v_ref_3839_);
    return v_res_3847_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    v___x_3849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_3850_ = l_Lean_stringToMessageData(v___x_3849_);
    return v___x_3850_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_3853_ = l_Lean_stringToMessageData(v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_ref_3854_: *mut LeanObject,
    mut v_constName_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    v___x_3861_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_3862_ = 0;
    lean_inc(v_constName_3855_);
    v___x_3863_ = l_Lean_MessageData_ofConstName(v_constName_3855_, v___x_3862_);
    v___x_3864_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3864_, 0, v___x_3861_);
    lean_ctor_set(v___x_3864_, 1, v___x_3863_);
    v___x_3865_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_3866_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3866_, 0, v___x_3864_);
    lean_ctor_set(v___x_3866_, 1, v___x_3865_);
    v___x_3867_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3854_, v___x_3866_, v_constName_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_3868_: *mut LeanObject,
    mut v_constName_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ref_3868_, v_constName_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
    lean_dec(v___y_3873_);
    lean_dec_ref(v___y_3872_);
    lean_dec(v___y_3871_);
    lean_dec_ref(v___y_3870_);
    lean_dec(v_ref_3868_);
    return v_res_3875_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_constName_3876_: *mut LeanObject,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
    mut v___y_3879_: *mut LeanObject,
    mut v___y_3880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3882_ = lean_ctor_get(v___y_3879_, 5);
    v___x_3883_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ref_3882_, v_constName_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
    return v___x_3883_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_constName_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
    mut v___y_3889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3890_: *mut LeanObject = core::ptr::null_mut();
    v_res_3890_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
    lean_dec(v___y_3888_);
    lean_dec_ref(v___y_3887_);
    lean_dec(v___y_3886_);
    lean_dec_ref(v___y_3885_);
    return v_res_3890_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0(
    mut v_constName_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3905_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3897_ = lean_st_ref_get(v___y_3895_);
                v_env_3898_ = lean_ctor_get(v___x_3897_, 0);
                lean_inc_ref(v_env_3898_);
                lean_dec(v___x_3897_);
                v___x_3899_ = 0;
                lean_inc(v_constName_3891_);
                v___x_3900_ =
                    l_Lean_Environment_find_x3f(v_env_3898_, v_constName_3891_, v___x_3899_);
                if lean_obj_tag(v___x_3900_) == 0 {
                    v___x_3901_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
                    return v___x_3901_;
                } else {
                    lean_dec(v_constName_3891_);
                    v_val_3902_ = lean_ctor_get(v___x_3900_, 0);
                    v_isSharedCheck_3909_ = (!lean_is_exclusive(v___x_3900_)) as u8;
                    if v_isSharedCheck_3909_ == 0 {
                        v___x_3904_ = v___x_3900_;
                        v_isShared_3905_ = v_isSharedCheck_3909_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3902_);
                        lean_dec(v___x_3900_);
                        v___x_3904_ = lean_box(0);
                        v_isShared_3905_ = v_isSharedCheck_3909_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3905_ == 0 {
                    lean_ctor_set_tag(v___x_3904_, 0);
                    v___x_3907_ = v___x_3904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_val_3902_);
                    v___x_3907_ = v_reuseFailAlloc_3908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0___boxed(
    mut v_constName_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3916_: *mut LeanObject = core::ptr::null_mut();
    v_res_3916_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0(v_constName_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
    lean_dec(v___y_3914_);
    lean_dec_ref(v___y_3913_);
    lean_dec(v___y_3912_);
    lean_dec_ref(v___y_3911_);
    return v_res_3916_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u64 = 0;
    v___x_3923_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_3924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3923_);
    return v___x_3924_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3925_: u64 = 0;
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    v___x_3925_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_3926_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_3927_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_3927_, 0, v___x_3926_);
    lean_ctor_set_uint64(
        v___x_3927_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3925_,
    );
    return v___x_3927_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    v___x_3928_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3928_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    v___x_3929_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_3930_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3930_, 0, v___x_3929_);
    return v___x_3930_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    v___x_3931_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_3932_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3932_, 0, v___x_3931_);
    lean_ctor_set(v___x_3932_, 1, v___x_3931_);
    lean_ctor_set(v___x_3932_, 2, v___x_3931_);
    lean_ctor_set(v___x_3932_, 3, v___x_3931_);
    lean_ctor_set(v___x_3932_, 4, v___x_3931_);
    lean_ctor_set(v___x_3932_, 5, v___x_3931_);
    return v___x_3932_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v___x_3933_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_3934_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3934_, 0, v___x_3933_);
    lean_ctor_set(v___x_3934_, 1, v___x_3933_);
    lean_ctor_set(v___x_3934_, 2, v___x_3933_);
    lean_ctor_set(v___x_3934_, 3, v___x_3933_);
    lean_ctor_set(v___x_3934_, 4, v___x_3933_);
    return v___x_3934_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: u64 = 0;
    v___x_3935_ = 2;
    v___x_3936_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    v___x_3938_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_3939_ = l_Lean_stringToMessageData(v___x_3938_);
    return v___x_3939_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_(
    mut v___x_3940_: *mut LeanObject,
    mut v___x_3941_: *mut LeanObject,
    mut v_decl_3942_: *mut LeanObject,
    mut v_x_3943_: *mut LeanObject,
    mut v_kind_3944_: u8,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: usize = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3981_: u8 = 0;
    let mut v_ctxApprox_3982_: u8 = 0;
    let mut v_quasiPatternApprox_3983_: u8 = 0;
    let mut v_constApprox_3984_: u8 = 0;
    let mut v_isDefEqStuckEx_3985_: u8 = 0;
    let mut v_unificationHints_3986_: u8 = 0;
    let mut v_proofIrrelevance_3987_: u8 = 0;
    let mut v_assignSyntheticOpaque_3988_: u8 = 0;
    let mut v_offsetCnstrs_3989_: u8 = 0;
    let mut v_etaStruct_3990_: u8 = 0;
    let mut v_univApprox_3991_: u8 = 0;
    let mut v_iota_3992_: u8 = 0;
    let mut v_beta_3993_: u8 = 0;
    let mut v_proj_3994_: u8 = 0;
    let mut v_zeta_3995_: u8 = 0;
    let mut v_zetaDelta_3996_: u8 = 0;
    let mut v_zetaUnused_3997_: u8 = 0;
    let mut v_zetaHave_3998_: u8 = 0;
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: u8 = 0;
    let mut v___x_4004_: u8 = 0;
    let mut v_config_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u64 = 0;
    let mut v___x_4008_: u64 = 0;
    let mut v___x_4009_: u64 = 0;
    let mut v___x_4010_: u64 = 0;
    let mut v___x_4011_: u64 = 0;
    let mut v_key_4012_: u64 = 0;
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v_snd_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_reuseFailAlloc_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut v_unused_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_a_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3948_ = 0;
                v___x_3949_ = 1;
                v___x_3950_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v___x_3951_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v___x_3952_ = lean_unsigned_to_nat(32);
                v___x_3953_ = lean_mk_empty_array_with_capacity(v___x_3952_);
                v___x_3954_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__3);
                v___x_3955_ = 5usize;
                lean_inc_n(v___x_3940_, 7);
                v___x_3956_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                lean_ctor_set(v___x_3956_, 1, v___x_3953_);
                lean_ctor_set(v___x_3956_, 2, v___x_3940_);
                lean_ctor_set(v___x_3956_, 3, v___x_3940_);
                lean_ctor_set_usize(v___x_3956_, 4, v___x_3955_);
                v___x_3957_ = lean_box(1);
                lean_inc_ref(v___x_3956_);
                v___x_3958_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3958_, 0, v___x_3951_);
                lean_ctor_set(v___x_3958_, 1, v___x_3956_);
                lean_ctor_set(v___x_3958_, 2, v___x_3957_);
                v___x_3959_ = lean_mk_empty_array_with_capacity(v___x_3940_);
                v___x_3960_ = lean_box(0);
                lean_inc_ref(v___x_3959_);
                lean_inc_ref(v___x_3958_);
                lean_inc_n(v___x_3941_, 2);
                v___x_3961_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_3961_, 0, v___x_3950_);
                lean_ctor_set(v___x_3961_, 1, v___x_3941_);
                lean_ctor_set(v___x_3961_, 2, v___x_3958_);
                lean_ctor_set(v___x_3961_, 3, v___x_3959_);
                lean_ctor_set(v___x_3961_, 4, v___x_3960_);
                lean_ctor_set(v___x_3961_, 5, v___x_3940_);
                lean_ctor_set(v___x_3961_, 6, v___x_3960_);
                lean_ctor_set_uint8(
                    v___x_3961_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_3948_,
                );
                lean_ctor_set_uint8(
                    v___x_3961_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_3948_,
                );
                lean_ctor_set_uint8(
                    v___x_3961_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_3948_,
                );
                lean_ctor_set_uint8(
                    v___x_3961_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_3949_,
                );
                v___x_3962_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_3962_, 0, v___x_3940_);
                lean_ctor_set(v___x_3962_, 1, v___x_3940_);
                lean_ctor_set(v___x_3962_, 2, v___x_3940_);
                lean_ctor_set(v___x_3962_, 3, v___x_3940_);
                lean_ctor_set(v___x_3962_, 4, v___x_3951_);
                lean_ctor_set(v___x_3962_, 5, v___x_3951_);
                lean_ctor_set(v___x_3962_, 6, v___x_3951_);
                lean_ctor_set(v___x_3962_, 7, v___x_3951_);
                lean_ctor_set(v___x_3962_, 8, v___x_3951_);
                lean_ctor_set(v___x_3962_, 9, v___x_3951_);
                v___x_3963_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v___x_3964_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v___x_3965_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3965_, 0, v___x_3962_);
                lean_ctor_set(v___x_3965_, 1, v___x_3963_);
                lean_ctor_set(v___x_3965_, 2, v___x_3941_);
                lean_ctor_set(v___x_3965_, 3, v___x_3956_);
                lean_ctor_set(v___x_3965_, 4, v___x_3964_);
                v___x_3966_ = lean_st_mk_ref(v___x_3965_);
                lean_inc(v_decl_3942_);
                v___x_3978_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0(v_decl_3942_, v___x_3961_, v___x_3966_, v___y_3945_, v___y_3946_);
                if lean_obj_tag(v___x_3978_) == 0 {
                    v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
                    lean_inc(v_a_3979_);
                    lean_dec_ref_known(v___x_3978_, 1);
                    v___x_3980_ = l_Lean_Meta_Context_config(v___x_3961_);
                    v_foApprox_3981_ = lean_ctor_get_uint8(v___x_3980_, 0 as u32);
                    v_ctxApprox_3982_ = lean_ctor_get_uint8(v___x_3980_, 1 as u32);
                    v_quasiPatternApprox_3983_ = lean_ctor_get_uint8(v___x_3980_, 2 as u32);
                    v_constApprox_3984_ = lean_ctor_get_uint8(v___x_3980_, 3 as u32);
                    v_isDefEqStuckEx_3985_ = lean_ctor_get_uint8(v___x_3980_, 4 as u32);
                    v_unificationHints_3986_ = lean_ctor_get_uint8(v___x_3980_, 5 as u32);
                    v_proofIrrelevance_3987_ = lean_ctor_get_uint8(v___x_3980_, 6 as u32);
                    v_assignSyntheticOpaque_3988_ = lean_ctor_get_uint8(v___x_3980_, 7 as u32);
                    v_offsetCnstrs_3989_ = lean_ctor_get_uint8(v___x_3980_, 8 as u32);
                    v_etaStruct_3990_ = lean_ctor_get_uint8(v___x_3980_, 10 as u32);
                    v_univApprox_3991_ = lean_ctor_get_uint8(v___x_3980_, 11 as u32);
                    v_iota_3992_ = lean_ctor_get_uint8(v___x_3980_, 12 as u32);
                    v_beta_3993_ = lean_ctor_get_uint8(v___x_3980_, 13 as u32);
                    v_proj_3994_ = lean_ctor_get_uint8(v___x_3980_, 14 as u32);
                    v_zeta_3995_ = lean_ctor_get_uint8(v___x_3980_, 15 as u32);
                    v_zetaDelta_3996_ = lean_ctor_get_uint8(v___x_3980_, 16 as u32);
                    v_zetaUnused_3997_ = lean_ctor_get_uint8(v___x_3980_, 17 as u32);
                    v_zetaHave_3998_ = lean_ctor_get_uint8(v___x_3980_, 18 as u32);
                    v_isSharedCheck_4077_ = (!lean_is_exclusive(v___x_3980_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4000_ = v___x_3980_;
                        v_isShared_4001_ = v_isSharedCheck_4077_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_3980_);
                        v___x_4000_ = lean_box(0);
                        v_isShared_4001_ = v_isSharedCheck_4077_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3966_);
                    lean_dec_ref_known(v___x_3961_, 7);
                    lean_dec_ref(v___x_3959_);
                    lean_dec_ref_known(v___x_3958_, 3);
                    lean_dec(v_decl_3942_);
                    lean_dec(v___x_3941_);
                    lean_dec(v___x_3940_);
                    v_a_4078_ = lean_ctor_get(v___x_3978_, 0);
                    v_isSharedCheck_4085_ = (!lean_is_exclusive(v___x_3978_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_3978_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_4078_);
                        lean_dec(v___x_3978_);
                        v___x_4080_ = lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3968_) == 0 {
                    v_a_3969_ = lean_ctor_get(v___y_3968_, 0);
                    v_isSharedCheck_3977_ = (!lean_is_exclusive(v___y_3968_)) as u8;
                    if v_isSharedCheck_3977_ == 0 {
                        v___x_3971_ = v___y_3968_;
                        v_isShared_3972_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3969_);
                        lean_dec(v___y_3968_);
                        v___x_3971_ = lean_box(0);
                        v_isShared_3972_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3966_);
                    return v___y_3968_;
                }
            }
            2 => {
                v___x_3973_ = lean_st_ref_get(v___x_3966_);
                lean_dec(v___x_3966_);
                lean_dec(v___x_3973_);
                if v_isShared_3972_ == 0 {
                    v___x_3975_ = v___x_3971_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3969_);
                    v___x_3975_ = v_reuseFailAlloc_3976_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3975_;
            }
            4 => {
                v___x_4002_ = l_Lean_ConstantInfo_type(v_a_3979_);
                lean_dec(v_a_3979_);
                v___x_4003_ = 0;
                v___x_4004_ = 2;
                if v_isShared_4001_ == 0 {
                    v_config_4006_ = v___x_4000_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 0 as u32, v_foApprox_3981_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 1 as u32, v_ctxApprox_3982_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4076_,
                        2 as u32,
                        v_quasiPatternApprox_3983_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 3 as u32, v_constApprox_3984_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 4 as u32, v_isDefEqStuckEx_3985_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 5 as u32, v_unificationHints_3986_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 6 as u32, v_proofIrrelevance_3987_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4076_,
                        7 as u32,
                        v_assignSyntheticOpaque_3988_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 8 as u32, v_offsetCnstrs_3989_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 10 as u32, v_etaStruct_3990_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 11 as u32, v_univApprox_3991_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 12 as u32, v_iota_3992_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 13 as u32, v_beta_3993_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 14 as u32, v_proj_3994_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 15 as u32, v_zeta_3995_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 16 as u32, v_zetaDelta_3996_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 17 as u32, v_zetaUnused_3997_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4076_, 18 as u32, v_zetaHave_3998_);
                    v_config_4006_ = v_reuseFailAlloc_4076_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(v_config_4006_, 9 as u32, v___x_4004_);
                v___x_4007_ = l_Lean_Meta_Context_configKey(v___x_3961_);
                v___x_4008_ = 3u64;
                v___x_4009_ = lean_uint64_shift_right(v___x_4007_, v___x_4008_);
                v___x_4010_ = lean_uint64_shift_left(v___x_4009_, v___x_4008_);
                v___x_4011_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v_key_4012_ = lean_uint64_lor(v___x_4010_, v___x_4011_);
                v___x_4013_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4013_, 0, v_config_4006_);
                lean_ctor_set_uint64(
                    v___x_4013_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4012_,
                );
                v___x_4014_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4014_, 0, v___x_4013_);
                lean_ctor_set(v___x_4014_, 1, v___x_3941_);
                lean_ctor_set(v___x_4014_, 2, v___x_3958_);
                lean_ctor_set(v___x_4014_, 3, v___x_3959_);
                lean_ctor_set(v___x_4014_, 4, v___x_3960_);
                lean_ctor_set(v___x_4014_, 5, v___x_3940_);
                lean_ctor_set(v___x_4014_, 6, v___x_3960_);
                lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_3948_,
                );
                lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_3948_,
                );
                lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_3948_,
                );
                lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_3949_,
                );
                lean_inc_ref(v___x_4002_);
                v___x_4015_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v___x_4002_,
                    v___x_3960_,
                    v___x_4003_,
                    v___x_4014_,
                    v___x_3966_,
                    v___y_3945_,
                    v___y_3946_,
                );
                if lean_obj_tag(v___x_4015_) == 0 {
                    v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
                    lean_inc(v_a_4016_);
                    lean_dec_ref_known(v___x_4015_, 1);
                    v_snd_4017_ = lean_ctor_get(v_a_4016_, 1);
                    v_fst_4018_ = lean_ctor_get(v_a_4016_, 0);
                    v_isSharedCheck_4067_ = (!lean_is_exclusive(v_a_4016_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v___x_4020_ = v_a_4016_;
                        v_isShared_4021_ = v_isSharedCheck_4067_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_4017_);
                        lean_inc(v_fst_4018_);
                        lean_dec(v_a_4016_);
                        v___x_4020_ = lean_box(0);
                        v_isShared_4021_ = v_isSharedCheck_4067_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_4014_, 7);
                    lean_dec_ref(v___x_4002_);
                    lean_dec(v___x_3966_);
                    lean_dec_ref_known(v___x_3961_, 7);
                    lean_dec(v_decl_3942_);
                    v_a_4068_ = lean_ctor_get(v___x_4015_, 0);
                    v_isSharedCheck_4075_ = (!lean_is_exclusive(v___x_4015_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4070_ = v___x_4015_;
                        v_isShared_4071_ = v_isSharedCheck_4075_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4068_);
                        lean_dec(v___x_4015_);
                        v___x_4070_ = lean_box(0);
                        v_isShared_4071_ = v_isSharedCheck_4075_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v_snd_4022_ = lean_ctor_get(v_snd_4017_, 1);
                v_isSharedCheck_4065_ = (!lean_is_exclusive(v_snd_4017_)) as u8;
                if v_isSharedCheck_4065_ == 0 {
                    v_unused_4066_ = lean_ctor_get(v_snd_4017_, 0);
                    lean_dec(v_unused_4066_);
                    v___x_4024_ = v_snd_4017_;
                    v_isShared_4025_ = v_isSharedCheck_4065_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_4022_);
                    lean_dec(v_snd_4017_);
                    v___x_4024_ = lean_box(0);
                    v_isShared_4025_ = v_isSharedCheck_4065_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4026_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v___x_4027_ = l_Lean_MessageData_ofExpr(v___x_4002_);
                if v_isShared_4021_ == 0 {
                    lean_ctor_set_tag(v___x_4020_, 7);
                    lean_ctor_set(v___x_4020_, 1, v___x_4027_);
                    lean_ctor_set(v___x_4020_, 0, v___x_4026_);
                    v___x_4029_ = v___x_4020_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4026_);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4027_);
                    v___x_4029_ = v_reuseFailAlloc_4064_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4030_ = lean_array_get_size(v_fst_4018_);
                lean_dec(v_fst_4018_);
                v___x_4031_ = lean_unsigned_to_nat(1);
                v___x_4032_ = lean_nat_sub(v___x_4030_, v___x_4031_);
                v___x_4033_ = lean_nat_dec_lt(v___x_4032_, v___x_4030_);
                lean_dec(v___x_4032_);
                if v___x_4033_ == 0 {
                    lean_del_object(v___x_4024_);
                    lean_dec(v_snd_4022_);
                    lean_dec_ref_known(v___x_4014_, 7);
                    lean_dec(v_decl_3942_);
                    v___x_4034_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4029_, v___x_3961_, v___x_3966_, v___y_3945_, v___y_3946_);
                    lean_dec_ref_known(v___x_3961_, 7);
                    v___y_3968_ = v___x_4034_;
                    state = 1;
                    continue;
                } else {
                    v___x_4035_ = l_Lean_Meta_reduce(
                        v_snd_4022_,
                        v___x_3949_,
                        v___x_3949_,
                        v___x_3949_,
                        v___x_3961_,
                        v___x_3966_,
                        v___y_3945_,
                        v___y_3946_,
                    );
                    if lean_obj_tag(v___x_4035_) == 0 {
                        v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
                        lean_inc(v_a_4036_);
                        lean_dec_ref_known(v___x_4035_, 1);
                        if lean_obj_tag(v_a_4036_) == 5 {
                            v_fn_4037_ = lean_ctor_get(v_a_4036_, 0);
                            lean_inc_ref(v_fn_4037_);
                            lean_dec_ref_known(v_a_4036_, 2);
                            if lean_obj_tag(v_fn_4037_) == 5 {
                                lean_dec_ref(v___x_4029_);
                                lean_dec_ref_known(v___x_3961_, 7);
                                v_fn_4038_ = lean_ctor_get(v_fn_4037_, 0);
                                lean_inc_ref(v_fn_4038_);
                                lean_dec_ref_known(v_fn_4037_, 2);
                                v___x_4039_ = l_Lean_Meta_DiscrTree_mkPath(
                                    v_fn_4038_,
                                    v___x_3948_,
                                    v___x_4014_,
                                    v___x_3966_,
                                    v___y_3945_,
                                    v___y_3946_,
                                );
                                lean_dec_ref_known(v___x_4014_, 7);
                                if lean_obj_tag(v___x_4039_) == 0 {
                                    v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
                                    lean_inc(v_a_4040_);
                                    lean_dec_ref_known(v___x_4039_, 1);
                                    v___x_4041_ = l_Lean_Meta_Symm_symmExt;
                                    if v_isShared_4025_ == 0 {
                                        lean_ctor_set(v___x_4024_, 1, v_a_4040_);
                                        lean_ctor_set(v___x_4024_, 0, v_decl_3942_);
                                        v___x_4043_ = v___x_4024_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_decl_3942_);
                                        lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_a_4040_);
                                        v___x_4043_ = v_reuseFailAlloc_4045_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_4024_);
                                    lean_dec(v___x_3966_);
                                    lean_dec(v_decl_3942_);
                                    v_a_4046_ = lean_ctor_get(v___x_4039_, 0);
                                    v_isSharedCheck_4053_ = (!lean_is_exclusive(v___x_4039_)) as u8;
                                    if v_isSharedCheck_4053_ == 0 {
                                        v___x_4048_ = v___x_4039_;
                                        v_isShared_4049_ = v_isSharedCheck_4053_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4046_);
                                        lean_dec(v___x_4039_);
                                        v___x_4048_ = lean_box(0);
                                        v_isShared_4049_ = v_isSharedCheck_4053_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_fn_4037_);
                                lean_del_object(v___x_4024_);
                                lean_dec_ref_known(v___x_4014_, 7);
                                lean_dec(v_decl_3942_);
                                v___x_4054_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4029_, v___x_3961_, v___x_3966_, v___y_3945_, v___y_3946_);
                                lean_dec_ref_known(v___x_3961_, 7);
                                v___y_3968_ = v___x_4054_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4036_);
                            lean_del_object(v___x_4024_);
                            lean_dec_ref_known(v___x_4014_, 7);
                            lean_dec(v_decl_3942_);
                            v___x_4055_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4029_, v___x_3961_, v___x_3966_, v___y_3945_, v___y_3946_);
                            lean_dec_ref_known(v___x_3961_, 7);
                            v___y_3968_ = v___x_4055_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4029_);
                        lean_del_object(v___x_4024_);
                        lean_dec_ref_known(v___x_4014_, 7);
                        lean_dec(v___x_3966_);
                        lean_dec_ref_known(v___x_3961_, 7);
                        lean_dec(v_decl_3942_);
                        v_a_4056_ = lean_ctor_get(v___x_4035_, 0);
                        v_isSharedCheck_4063_ = (!lean_is_exclusive(v___x_4035_)) as u8;
                        if v_isSharedCheck_4063_ == 0 {
                            v___x_4058_ = v___x_4035_;
                            v_isShared_4059_ = v_isSharedCheck_4063_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_4056_);
                            lean_dec(v___x_4035_);
                            v___x_4058_ = lean_box(0);
                            v_isShared_4059_ = v_isSharedCheck_4063_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_4044_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__2___redArg(v___x_4041_, v___x_4043_, v_kind_3944_, v___x_3966_, v___y_3945_, v___y_3946_);
                v___y_3968_ = v___x_4044_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4049_ == 0 {
                    v___x_4051_ = v___x_4048_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
                    v___x_4051_ = v_reuseFailAlloc_4052_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4051_;
            }
            12 => {
                if v_isShared_4059_ == 0 {
                    v___x_4061_ = v___x_4058_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
                    v___x_4061_ = v_reuseFailAlloc_4062_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4061_;
            }
            14 => {
                if v_isShared_4071_ == 0 {
                    v___x_4073_ = v___x_4070_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
                    v___x_4073_ = v_reuseFailAlloc_4074_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4073_;
            }
            16 => {
                if v_isShared_4081_ == 0 {
                    v___x_4083_ = v___x_4080_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2____boxed(
    mut v___x_4086_: *mut LeanObject,
    mut v___x_4087_: *mut LeanObject,
    mut v_decl_4088_: *mut LeanObject,
    mut v_x_4089_: *mut LeanObject,
    mut v_kind_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4094_: u8 = 0;
    let mut v_res_4095_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4094_ = (lean_unbox(v_kind_4090_) as u8);
    v_res_4095_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_(v___x_4086_, v___x_4087_, v_decl_4088_, v_x_4089_, v_kind_boxed_4094_, v___y_4091_, v___y_4092_);
    lean_dec(v___y_4092_);
    lean_dec_ref(v___y_4091_);
    lean_dec(v_x_4089_);
    return v_res_4095_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3_spec__5(
    mut v_msgData_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    v___x_4100_ = lean_st_ref_get(v___y_4098_);
    v_env_4101_ = lean_ctor_get(v___x_4100_, 0);
    lean_inc_ref(v_env_4101_);
    lean_dec(v___x_4100_);
    v_options_4102_ = lean_ctor_get(v___y_4097_, 2);
    v___x_4103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__2);
    v___x_4104_ = lean_unsigned_to_nat(32);
    v___x_4105_ = lean_mk_empty_array_with_capacity(v___x_4104_);
    lean_dec_ref(v___x_4105_);
    v___x_4106_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg___closed__5);
    lean_inc_ref(v_options_4102_);
    v___x_4107_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4107_, 0, v_env_4101_);
    lean_ctor_set(v___x_4107_, 1, v___x_4103_);
    lean_ctor_set(v___x_4107_, 2, v___x_4106_);
    lean_ctor_set(v___x_4107_, 3, v_options_4102_);
    v___x_4108_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4108_, 0, v___x_4107_);
    lean_ctor_set(v___x_4108_, 1, v_msgData_4096_);
    v___x_4109_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4109_, 0, v___x_4108_);
    return v___x_4109_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3_spec__5___boxed(
    mut v_msgData_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4114_: *mut LeanObject = core::ptr::null_mut();
    v_res_4114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3_spec__5(v_msgData_4110_, v___y_4111_, v___y_4112_);
    lean_dec(v___y_4112_);
    lean_dec_ref(v___y_4111_);
    return v_res_4114_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3___redArg(
    mut v_msg_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4119_ = lean_ctor_get(v___y_4116_, 5);
                v___x_4120_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3_spec__5(v_msg_4115_, v___y_4116_, v___y_4117_);
                v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
                v_isSharedCheck_4129_ = (!lean_is_exclusive(v___x_4120_)) as u8;
                if v_isSharedCheck_4129_ == 0 {
                    v___x_4123_ = v___x_4120_;
                    v_isShared_4124_ = v_isSharedCheck_4129_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4121_);
                    lean_dec(v___x_4120_);
                    v___x_4123_ = lean_box(0);
                    v_isShared_4124_ = v_isSharedCheck_4129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4119_);
                v___x_4125_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4125_, 0, v_ref_4119_);
                lean_ctor_set(v___x_4125_, 1, v_a_4121_);
                if v_isShared_4124_ == 0 {
                    lean_ctor_set_tag(v___x_4123_, 1);
                    lean_ctor_set(v___x_4123_, 0, v___x_4125_);
                    v___x_4127_ = v___x_4123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3___redArg___boxed(
    mut v_msg_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4134_: *mut LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3___redArg(v_msg_4130_, v___y_4131_, v___y_4132_);
    lean_dec(v___y_4132_);
    lean_dec_ref(v___y_4131_);
    return v_res_4134_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    v___x_4136_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4137_ = l_Lean_stringToMessageData(v___x_4136_);
    return v___x_4137_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4139_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4140_ = l_Lean_stringToMessageData(v___x_4139_);
    return v___x_4140_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_(
    mut v___x_4141_: *mut LeanObject,
    mut v_decl_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    v___x_4146_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4147_ = l_Lean_MessageData_ofName(v___x_4141_);
    v___x_4148_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4148_, 0, v___x_4146_);
    lean_ctor_set(v___x_4148_, 1, v___x_4147_);
    v___x_4149_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4150_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4150_, 0, v___x_4148_);
    lean_ctor_set(v___x_4150_, 1, v___x_4149_);
    v___x_4151_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3___redArg(v___x_4150_, v___y_4143_, v___y_4144_);
    return v___x_4151_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2____boxed(
    mut v___x_4152_: *mut LeanObject,
    mut v_decl_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4157_: *mut LeanObject = core::ptr::null_mut();
    v_res_4157_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_(v___x_4152_, v_decl_4153_, v___y_4154_, v___y_4155_);
    lean_dec(v___y_4155_);
    lean_dec_ref(v___y_4154_);
    lean_dec(v_decl_4153_);
    return v_res_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__20_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v___x_4210_ = lean_unsigned_to_nat(3447505512);
    v___x_4211_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__19_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4212_ = l_Lean_Name_num___override(v___x_4211_, v___x_4210_);
    return v___x_4212_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__22_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    v___x_4214_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__21_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4215_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__20_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__20_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__20_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4216_ = l_Lean_Name_str___override(v___x_4215_, v___x_4214_);
    return v___x_4216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__24_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    v___x_4218_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__23_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4219_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__22_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__22_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__22_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4220_ = l_Lean_Name_str___override(v___x_4219_, v___x_4218_);
    return v___x_4220_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    v___x_4221_ = lean_unsigned_to_nat(2);
    v___x_4222_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__24_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__24_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__24_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4223_ = l_Lean_Name_num___override(v___x_4222_, v___x_4221_);
    return v___x_4223_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__30_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    v___x_4230_ = 0;
    v___x_4231_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__29_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4232_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__27_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4233_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4234_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_4234_, 0, v___x_4233_);
    lean_ctor_set(v___x_4234_, 1, v___x_4232_);
    lean_ctor_set(v___x_4234_, 2, v___x_4231_);
    lean_ctor_set_uint8(
        v___x_4234_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4230_,
    );
    return v___x_4234_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__31_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v___f_4235_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__28_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___f_4236_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4237_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__30_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__30_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__30_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4238_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4238_, 0, v___x_4237_);
    lean_ctor_set(v___x_4238_, 1, v___f_4236_);
    lean_ctor_set(v___x_4238_, 2, v___f_4235_);
    return v___x_4238_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    v___x_4240_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__31_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__31_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__31_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4241_ = l_Lean_registerBuiltinAttribute(v___x_4240_);
    return v___x_4241_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2____boxed(
    mut v_a_4242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4243_: *mut LeanObject = core::ptr::null_mut();
    v_res_4243_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_();
    return v_res_4243_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_4244_: *mut LeanObject,
    mut v_msg_4245_: *mut LeanObject,
    mut v___y_4246_: *mut LeanObject,
    mut v___y_4247_: *mut LeanObject,
    mut v___y_4248_: *mut LeanObject,
    mut v___y_4249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    v___x_4251_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v_msg_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
    return v___x_4251_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_4252_: *mut LeanObject,
    mut v_msg_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
    mut v___y_4257_: *mut LeanObject,
    mut v___y_4258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4259_: *mut LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1(v_00_u03b1_4252_, v_msg_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
    lean_dec(v___y_4257_);
    lean_dec_ref(v___y_4256_);
    lean_dec(v___y_4255_);
    lean_dec_ref(v___y_4254_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3(
    mut v_00_u03b1_4260_: *mut LeanObject,
    mut v_msg_4261_: *mut LeanObject,
    mut v___y_4262_: *mut LeanObject,
    mut v___y_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    v___x_4265_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3___redArg(v_msg_4261_, v___y_4262_, v___y_4263_);
    return v___x_4265_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3___boxed(
    mut v_00_u03b1_4266_: *mut LeanObject,
    mut v_msg_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4271_: *mut LeanObject = core::ptr::null_mut();
    v_res_4271_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__3(v_00_u03b1_4266_, v_msg_4267_, v___y_4268_, v___y_4269_);
    lean_dec(v___y_4269_);
    lean_dec_ref(v___y_4268_);
    return v_res_4271_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_4272_: *mut LeanObject,
    mut v_constName_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    v___x_4279_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
    return v___x_4279_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_4280_: *mut LeanObject,
    mut v_constName_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
    mut v___y_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4287_: *mut LeanObject = core::ptr::null_mut();
    v_res_4287_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_4280_, v_constName_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
    lean_dec(v___y_4285_);
    lean_dec_ref(v___y_4284_);
    lean_dec(v___y_4283_);
    lean_dec_ref(v___y_4282_);
    return v_res_4287_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_00_u03b1_4288_: *mut LeanObject,
    mut v_ref_4289_: *mut LeanObject,
    mut v_constName_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4296_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ref_4289_, v_constName_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
    return v___x_4296_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_4297_: *mut LeanObject,
    mut v_ref_4298_: *mut LeanObject,
    mut v_constName_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4305_: *mut LeanObject = core::ptr::null_mut();
    v_res_4305_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b1_4297_, v_ref_4298_, v_constName_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
    lean_dec(v___y_4303_);
    lean_dec_ref(v___y_4302_);
    lean_dec(v___y_4301_);
    lean_dec_ref(v___y_4300_);
    lean_dec(v_ref_4298_);
    return v_res_4305_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(
    mut v_00_u03b1_4306_: *mut LeanObject,
    mut v_ref_4307_: *mut LeanObject,
    mut v_msg_4308_: *mut LeanObject,
    mut v_declHint_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    v___x_4315_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_ref_4307_, v_msg_4308_, v_declHint_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
    return v___x_4315_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_00_u03b1_4316_: *mut LeanObject,
    mut v_ref_4317_: *mut LeanObject,
    mut v_msg_4318_: *mut LeanObject,
    mut v_declHint_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4325_: *mut LeanObject = core::ptr::null_mut();
    v_res_4325_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_4316_, v_ref_4317_, v_msg_4318_, v_declHint_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
    lean_dec(v___y_4323_);
    lean_dec_ref(v___y_4322_);
    lean_dec(v___y_4321_);
    lean_dec_ref(v___y_4320_);
    lean_dec(v_ref_4317_);
    return v_res_4325_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9(
    mut v_msg_4326_: *mut LeanObject,
    mut v_declHint_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    v___x_4333_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___redArg(v_msg_4326_, v_declHint_4327_, v___y_4331_);
    return v___x_4333_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9___boxed(
    mut v_msg_4334_: *mut LeanObject,
    mut v_declHint_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4341_: *mut LeanObject = core::ptr::null_mut();
    v_res_4341_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__8_spec__9(v_msg_4334_, v_declHint_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
    lean_dec(v___y_4339_);
    lean_dec_ref(v___y_4338_);
    lean_dec(v___y_4337_);
    lean_dec_ref(v___y_4336_);
    return v_res_4341_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9(
    mut v_00_u03b1_4342_: *mut LeanObject,
    mut v_ref_4343_: *mut LeanObject,
    mut v_msg_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9___redArg(v_ref_4343_, v_msg_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
    return v___x_4350_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9___boxed(
    mut v_00_u03b1_4351_: *mut LeanObject,
    mut v_ref_4352_: *mut LeanObject,
    mut v_msg_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4359_: *mut LeanObject = core::ptr::null_mut();
    v_res_4359_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_spec__9(v_00_u03b1_4351_, v_ref_4352_, v_msg_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
    lean_dec(v___y_4357_);
    lean_dec_ref(v___y_4356_);
    lean_dec(v___y_4355_);
    lean_dec_ref(v___y_4354_);
    lean_dec(v_ref_4352_);
    return v_res_4359_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4362_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___closed__25_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
    v___x_4363_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_;
    v___x_4364_ = l_Lean_addBuiltinDocString(v___x_4362_, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2____boxed(
    mut v_a_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4366_: *mut LeanObject = core::ptr::null_mut();
    v_res_4366_ = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_();
    return v_res_4366_;
}
pub unsafe fn _init_l_Lean_Expr_getSymmLems___closed__1() -> *mut LeanObject {
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = l_Lean_Expr_getSymmLems___closed__0;
    v___x_4369_ = l_Lean_stringToMessageData(v___x_4368_);
    return v___x_4369_;
}
pub unsafe fn l_Lean_Expr_getSymmLems(
    mut v_tgt_4370_: *mut LeanObject,
    mut v_a_4371_: *mut LeanObject,
    mut v_a_4372_: *mut LeanObject,
    mut v_a_4373_: *mut LeanObject,
    mut v_a_4374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_tgt_4370_) == 5 {
                    v_fn_4385_ = lean_ctor_get(v_tgt_4370_, 0);
                    if lean_obj_tag(v_fn_4385_) == 5 {
                        lean_inc_ref(v_fn_4385_);
                        lean_dec_ref_known(v_tgt_4370_, 2);
                        v_fn_4386_ = lean_ctor_get(v_fn_4385_, 0);
                        lean_inc_ref(v_fn_4386_);
                        lean_dec_ref_known(v_fn_4385_, 2);
                        v___x_4387_ = lean_st_ref_get(v_a_4374_);
                        v_env_4388_ = lean_ctor_get(v___x_4387_, 0);
                        lean_inc_ref(v_env_4388_);
                        lean_dec(v___x_4387_);
                        v___x_4389_ = l_Lean_Meta_Symm_symmExt;
                        v_ext_4390_ = lean_ctor_get(v___x_4389_, 1);
                        v_toEnvExtension_4391_ = lean_ctor_get(v_ext_4390_, 0);
                        v_asyncMode_4392_ = lean_ctor_get(v_toEnvExtension_4391_, 2);
                        v___x_4393_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__3___closed__0);
                        v___x_4394_ = l_Lean_ScopedEnvExtension_getState___redArg(
                            v___x_4393_,
                            v___x_4389_,
                            v_env_4388_,
                            v_asyncMode_4392_,
                        );
                        v___x_4395_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
                            v___x_4394_,
                            v_fn_4386_,
                            v_a_4371_,
                            v_a_4372_,
                            v_a_4373_,
                            v_a_4374_,
                        );
                        lean_dec(v___x_4394_);
                        return v___x_4395_;
                    } else {
                        v___y_4377_ = v_a_4371_;
                        v___y_4378_ = v_a_4372_;
                        v___y_4379_ = v_a_4373_;
                        v___y_4380_ = v_a_4374_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_4377_ = v_a_4371_;
                    v___y_4378_ = v_a_4372_;
                    v___y_4379_ = v_a_4373_;
                    v___y_4380_ = v_a_4374_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4381_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Expr_getSymmLems___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Expr_getSymmLems___closed__1_once),
                    _init_l_Lean_Expr_getSymmLems___closed__1,
                );
                v___x_4382_ = l_Lean_indentExpr(v_tgt_4370_);
                v___x_4383_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4383_, 0, v___x_4381_);
                lean_ctor_set(v___x_4383_, 1, v___x_4382_);
                v___x_4384_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4383_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
                return v___x_4384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_getSymmLems___boxed(
    mut v_tgt_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
    mut v_a_4399_: *mut LeanObject,
    mut v_a_4400_: *mut LeanObject,
    mut v_a_4401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4402_: *mut LeanObject = core::ptr::null_mut();
    v_res_4402_ = l_Lean_Expr_getSymmLems(v_tgt_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
    lean_dec(v_a_4400_);
    lean_dec_ref(v_a_4399_);
    lean_dec(v_a_4398_);
    lean_dec_ref(v_a_4397_);
    return v_res_4402_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg(
    mut v_e_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4420_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_unused_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4406_ = l_Lean_Expr_hasMVar(v_e_4403_);
                if v___x_4406_ == 0 {
                    v___x_4407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4407_, 0, v_e_4403_);
                    return v___x_4407_;
                } else {
                    v___x_4408_ = lean_st_ref_get(v___y_4404_);
                    v_mctx_4409_ = lean_ctor_get(v___x_4408_, 0);
                    lean_inc_ref(v_mctx_4409_);
                    lean_dec(v___x_4408_);
                    v___x_4410_ = l_Lean_instantiateMVarsCore(v_mctx_4409_, v_e_4403_);
                    v_fst_4411_ = lean_ctor_get(v___x_4410_, 0);
                    lean_inc(v_fst_4411_);
                    v_snd_4412_ = lean_ctor_get(v___x_4410_, 1);
                    lean_inc(v_snd_4412_);
                    lean_dec_ref(v___x_4410_);
                    v___x_4413_ = lean_st_ref_take(v___y_4404_);
                    v_cache_4414_ = lean_ctor_get(v___x_4413_, 1);
                    v_zetaDeltaFVarIds_4415_ = lean_ctor_get(v___x_4413_, 2);
                    v_postponed_4416_ = lean_ctor_get(v___x_4413_, 3);
                    v_diag_4417_ = lean_ctor_get(v___x_4413_, 4);
                    v_isSharedCheck_4426_ = (!lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4426_ == 0 {
                        v_unused_4427_ = lean_ctor_get(v___x_4413_, 0);
                        lean_dec(v_unused_4427_);
                        v___x_4419_ = v___x_4413_;
                        v_isShared_4420_ = v_isSharedCheck_4426_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4417_);
                        lean_inc(v_postponed_4416_);
                        lean_inc(v_zetaDeltaFVarIds_4415_);
                        lean_inc(v_cache_4414_);
                        lean_dec(v___x_4413_);
                        v___x_4419_ = lean_box(0);
                        v_isShared_4420_ = v_isSharedCheck_4426_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4420_ == 0 {
                    lean_ctor_set(v___x_4419_, 0, v_snd_4412_);
                    v___x_4422_ = v___x_4419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_snd_4412_);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_cache_4414_);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_zetaDeltaFVarIds_4415_);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_postponed_4416_);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_diag_4417_);
                    v___x_4422_ = v_reuseFailAlloc_4425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4423_ = lean_st_ref_set(v___y_4404_, v___x_4422_);
                v___x_4424_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4424_, 0, v_fst_4411_);
                return v___x_4424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg___boxed(
    mut v_e_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4431_: *mut LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg(
        v_e_4428_,
        v___y_4429_,
    );
    lean_dec(v___y_4429_);
    return v_res_4431_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0(
    mut v_e_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    v___x_4438_ = l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg(
        v_e_4432_,
        v___y_4434_,
    );
    return v___x_4438_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___boxed(
    mut v_e_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4445_: *mut LeanObject = core::ptr::null_mut();
    v_res_4445_ = l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0(
        v_e_4439_,
        v___y_4440_,
        v___y_4441_,
        v___y_4442_,
        v___y_4443_,
    );
    lean_dec(v___y_4443_);
    lean_dec_ref(v___y_4442_);
    lean_dec(v___y_4441_);
    lean_dec_ref(v___y_4440_);
    return v_res_4445_;
}
pub unsafe fn _init_l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    v___x_4447_ = l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__0;
    v___x_4448_ = l_Lean_stringToMessageData(v___x_4447_);
    return v___x_4448_;
}
pub unsafe fn l_List_firstM___at___00Lean_Expr_applySymm_spec__1(
    mut v_a_4449_: *mut LeanObject,
    mut v_e_4450_: *mut LeanObject,
    mut v_x_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4465_: u8 = 0;
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v___y_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: u8 = 0;
    let mut v___x_4480_: u8 = 0;
    let mut v___y_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4490_: u8 = 0;
    let mut v_ctxApprox_4491_: u8 = 0;
    let mut v_quasiPatternApprox_4492_: u8 = 0;
    let mut v_constApprox_4493_: u8 = 0;
    let mut v_isDefEqStuckEx_4494_: u8 = 0;
    let mut v_unificationHints_4495_: u8 = 0;
    let mut v_proofIrrelevance_4496_: u8 = 0;
    let mut v_assignSyntheticOpaque_4497_: u8 = 0;
    let mut v_offsetCnstrs_4498_: u8 = 0;
    let mut v_etaStruct_4499_: u8 = 0;
    let mut v_univApprox_4500_: u8 = 0;
    let mut v_iota_4501_: u8 = 0;
    let mut v_beta_4502_: u8 = 0;
    let mut v_proj_4503_: u8 = 0;
    let mut v_zeta_4504_: u8 = 0;
    let mut v_zetaDelta_4505_: u8 = 0;
    let mut v_zetaUnused_4506_: u8 = 0;
    let mut v_zetaHave_4507_: u8 = 0;
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v_trackZetaDelta_4511_: u8 = 0;
    let mut v_zetaDeltaSet_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4518_: u8 = 0;
    let mut v_inTypeClassResolution_4519_: u8 = 0;
    let mut v_cacheInferType_4520_: u8 = 0;
    let mut v___x_4521_: u8 = 0;
    let mut v_config_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: u64 = 0;
    let mut v___x_4525_: u64 = 0;
    let mut v___x_4526_: u64 = 0;
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: u8 = 0;
    let mut v___x_4529_: u64 = 0;
    let mut v___x_4530_: u64 = 0;
    let mut v_key_4531_: u64 = 0;
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4556_: u8 = 0;
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v_a_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v_reuseFailAlloc_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_a_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_a_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4451_) == 0 {
                    lean_dec_ref(v_e_4450_);
                    v___x_4457_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1_once
                        ),
                        _init_l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1,
                    );
                    v___x_4458_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4457_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
                    return v___x_4458_;
                } else {
                    v_head_4459_ = lean_ctor_get(v_x_4451_, 0);
                    lean_inc(v_head_4459_);
                    v_tail_4460_ = lean_ctor_get(v_x_4451_, 1);
                    lean_inc(v_tail_4460_);
                    lean_dec_ref_known(v_x_4451_, 2);
                    v___x_4461_ = l_Lean_Meta_saveState___redArg(v___y_4453_, v___y_4455_);
                    if lean_obj_tag(v___x_4461_) == 0 {
                        v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
                        lean_inc(v_a_4462_);
                        lean_dec_ref_known(v___x_4461_, 1);
                        v___x_4484_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_4449_,
                            v___y_4453_,
                            v___y_4455_,
                        );
                        if lean_obj_tag(v___x_4484_) == 0 {
                            lean_dec_ref_known(v___x_4484_, 1);
                            v___x_4485_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                                v_head_4459_,
                                v___y_4452_,
                                v___y_4453_,
                                v___y_4454_,
                                v___y_4455_,
                            );
                            if lean_obj_tag(v___x_4485_) == 0 {
                                v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
                                lean_inc_n(v_a_4486_, 2);
                                lean_dec_ref_known(v___x_4485_, 1);
                                lean_inc(v___y_4455_);
                                lean_inc_ref(v___y_4454_);
                                lean_inc(v___y_4453_);
                                lean_inc_ref(v___y_4452_);
                                v___x_4487_ = lean_infer_type(
                                    v_a_4486_,
                                    v___y_4452_,
                                    v___y_4453_,
                                    v___y_4454_,
                                    v___y_4455_,
                                );
                                if lean_obj_tag(v___x_4487_) == 0 {
                                    v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
                                    lean_inc(v_a_4488_);
                                    lean_dec_ref_known(v___x_4487_, 1);
                                    v___x_4489_ = l_Lean_Meta_Context_config(v___y_4452_);
                                    v_foApprox_4490_ = lean_ctor_get_uint8(v___x_4489_, 0 as u32);
                                    v_ctxApprox_4491_ = lean_ctor_get_uint8(v___x_4489_, 1 as u32);
                                    v_quasiPatternApprox_4492_ =
                                        lean_ctor_get_uint8(v___x_4489_, 2 as u32);
                                    v_constApprox_4493_ =
                                        lean_ctor_get_uint8(v___x_4489_, 3 as u32);
                                    v_isDefEqStuckEx_4494_ =
                                        lean_ctor_get_uint8(v___x_4489_, 4 as u32);
                                    v_unificationHints_4495_ =
                                        lean_ctor_get_uint8(v___x_4489_, 5 as u32);
                                    v_proofIrrelevance_4496_ =
                                        lean_ctor_get_uint8(v___x_4489_, 6 as u32);
                                    v_assignSyntheticOpaque_4497_ =
                                        lean_ctor_get_uint8(v___x_4489_, 7 as u32);
                                    v_offsetCnstrs_4498_ =
                                        lean_ctor_get_uint8(v___x_4489_, 8 as u32);
                                    v_etaStruct_4499_ = lean_ctor_get_uint8(v___x_4489_, 10 as u32);
                                    v_univApprox_4500_ =
                                        lean_ctor_get_uint8(v___x_4489_, 11 as u32);
                                    v_iota_4501_ = lean_ctor_get_uint8(v___x_4489_, 12 as u32);
                                    v_beta_4502_ = lean_ctor_get_uint8(v___x_4489_, 13 as u32);
                                    v_proj_4503_ = lean_ctor_get_uint8(v___x_4489_, 14 as u32);
                                    v_zeta_4504_ = lean_ctor_get_uint8(v___x_4489_, 15 as u32);
                                    v_zetaDelta_4505_ = lean_ctor_get_uint8(v___x_4489_, 16 as u32);
                                    v_zetaUnused_4506_ =
                                        lean_ctor_get_uint8(v___x_4489_, 17 as u32);
                                    v_zetaHave_4507_ = lean_ctor_get_uint8(v___x_4489_, 18 as u32);
                                    v_isSharedCheck_4570_ = (!lean_is_exclusive(v___x_4489_)) as u8;
                                    if v_isSharedCheck_4570_ == 0 {
                                        v___x_4509_ = v___x_4489_;
                                        v_isShared_4510_ = v_isSharedCheck_4570_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_dec(v___x_4489_);
                                        v___x_4509_ = lean_box(0);
                                        v_isShared_4510_ = v_isSharedCheck_4570_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4486_);
                                    v___y_4482_ = v___x_4487_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___y_4482_ = v___x_4485_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_head_4459_);
                            v_a_4571_ = lean_ctor_get(v___x_4484_, 0);
                            v_isSharedCheck_4578_ = (!lean_is_exclusive(v___x_4484_)) as u8;
                            if v_isSharedCheck_4578_ == 0 {
                                v___x_4573_ = v___x_4484_;
                                v_isShared_4574_ = v_isSharedCheck_4578_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_4571_);
                                lean_dec(v___x_4484_);
                                v___x_4573_ = lean_box(0);
                                v_isShared_4574_ = v_isSharedCheck_4578_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_tail_4460_);
                        lean_dec(v_head_4459_);
                        lean_dec_ref(v_e_4450_);
                        v_a_4579_ = lean_ctor_get(v___x_4461_, 0);
                        v_isSharedCheck_4586_ = (!lean_is_exclusive(v___x_4461_)) as u8;
                        if v_isSharedCheck_4586_ == 0 {
                            v___x_4581_ = v___x_4461_;
                            v_isShared_4582_ = v_isSharedCheck_4586_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_4579_);
                            lean_dec(v___x_4461_);
                            v___x_4581_ = lean_box(0);
                            v_isShared_4582_ = v_isSharedCheck_4586_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_4465_ == 0 {
                    lean_dec_ref(v___y_4464_);
                    v___x_4466_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_4462_,
                        v___y_4453_,
                        v___y_4455_,
                    );
                    lean_dec(v_a_4462_);
                    if lean_obj_tag(v___x_4466_) == 0 {
                        lean_dec_ref_known(v___x_4466_, 1);
                        v_x_4451_ = v_tail_4460_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_4460_);
                        lean_dec_ref(v_e_4450_);
                        v_a_4468_ = lean_ctor_get(v___x_4466_, 0);
                        v_isSharedCheck_4475_ = (!lean_is_exclusive(v___x_4466_)) as u8;
                        if v_isSharedCheck_4475_ == 0 {
                            v___x_4470_ = v___x_4466_;
                            v_isShared_4471_ = v_isSharedCheck_4475_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4468_);
                            lean_dec(v___x_4466_);
                            v___x_4470_ = lean_box(0);
                            v_isShared_4471_ = v_isSharedCheck_4475_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4462_);
                    lean_dec(v_tail_4460_);
                    lean_dec_ref(v_e_4450_);
                    return v___y_4464_;
                }
            }
            2 => {
                if v_isShared_4471_ == 0 {
                    v___x_4473_ = v___x_4470_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4473_;
            }
            4 => {
                v___x_4479_ = l_Lean_Exception_isInterrupt(v_a_4478_);
                if v___x_4479_ == 0 {
                    v___x_4480_ = l_Lean_Exception_isRuntime(v_a_4478_);
                    v___y_4464_ = v___y_4477_;
                    v___y_4465_ = v___x_4480_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_a_4478_);
                    v___y_4464_ = v___y_4477_;
                    v___y_4465_ = v___x_4479_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v___y_4482_) == 0 {
                    lean_dec(v_a_4462_);
                    lean_dec(v_tail_4460_);
                    lean_dec_ref(v_e_4450_);
                    return v___y_4482_;
                } else {
                    v_a_4483_ = lean_ctor_get(v___y_4482_, 0);
                    lean_inc(v_a_4483_);
                    v___y_4477_ = v___y_4482_;
                    v_a_4478_ = v_a_4483_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_trackZetaDelta_4511_ = lean_ctor_get_uint8(
                    v___y_4452_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4512_ = lean_ctor_get(v___y_4452_, 1);
                v_lctx_4513_ = lean_ctor_get(v___y_4452_, 2);
                v_localInstances_4514_ = lean_ctor_get(v___y_4452_, 3);
                v_defEqCtx_x3f_4515_ = lean_ctor_get(v___y_4452_, 4);
                v_synthPendingDepth_4516_ = lean_ctor_get(v___y_4452_, 5);
                v_canUnfold_x3f_4517_ = lean_ctor_get(v___y_4452_, 6);
                v_univApprox_4518_ = lean_ctor_get_uint8(
                    v___y_4452_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4519_ = lean_ctor_get_uint8(
                    v___y_4452_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4520_ = lean_ctor_get_uint8(
                    v___y_4452_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_4521_ = 2;
                if v_isShared_4510_ == 0 {
                    v_config_4523_ = v___x_4509_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 0 as u32, v_foApprox_4490_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 1 as u32, v_ctxApprox_4491_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4569_,
                        2 as u32,
                        v_quasiPatternApprox_4492_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 3 as u32, v_constApprox_4493_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 4 as u32, v_isDefEqStuckEx_4494_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 5 as u32, v_unificationHints_4495_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 6 as u32, v_proofIrrelevance_4496_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4569_,
                        7 as u32,
                        v_assignSyntheticOpaque_4497_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 8 as u32, v_offsetCnstrs_4498_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 10 as u32, v_etaStruct_4499_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 11 as u32, v_univApprox_4500_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 12 as u32, v_iota_4501_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 13 as u32, v_beta_4502_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 14 as u32, v_proj_4503_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 15 as u32, v_zeta_4504_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 16 as u32, v_zetaDelta_4505_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 17 as u32, v_zetaUnused_4506_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4569_, 18 as u32, v_zetaHave_4507_);
                    v_config_4523_ = v_reuseFailAlloc_4569_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(v_config_4523_, 9 as u32, v___x_4521_);
                v___x_4524_ = l_Lean_Meta_Context_configKey(v___y_4452_);
                v___x_4525_ = 3u64;
                v___x_4526_ = lean_uint64_shift_right(v___x_4524_, v___x_4525_);
                v___x_4527_ = lean_box(0);
                v___x_4528_ = 0;
                v___x_4529_ = lean_uint64_shift_left(v___x_4526_, v___x_4525_);
                v___x_4530_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v_key_4531_ = lean_uint64_lor(v___x_4529_, v___x_4530_);
                v___x_4532_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4532_, 0, v_config_4523_);
                lean_ctor_set_uint64(
                    v___x_4532_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4531_,
                );
                lean_inc(v_canUnfold_x3f_4517_);
                lean_inc(v_synthPendingDepth_4516_);
                lean_inc(v_defEqCtx_x3f_4515_);
                lean_inc_ref(v_localInstances_4514_);
                lean_inc_ref(v_lctx_4513_);
                lean_inc(v_zetaDeltaSet_4512_);
                v___x_4533_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4533_, 0, v___x_4532_);
                lean_ctor_set(v___x_4533_, 1, v_zetaDeltaSet_4512_);
                lean_ctor_set(v___x_4533_, 2, v_lctx_4513_);
                lean_ctor_set(v___x_4533_, 3, v_localInstances_4514_);
                lean_ctor_set(v___x_4533_, 4, v_defEqCtx_x3f_4515_);
                lean_ctor_set(v___x_4533_, 5, v_synthPendingDepth_4516_);
                lean_ctor_set(v___x_4533_, 6, v_canUnfold_x3f_4517_);
                lean_ctor_set_uint8(
                    v___x_4533_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4511_,
                );
                lean_ctor_set_uint8(
                    v___x_4533_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4518_,
                );
                lean_ctor_set_uint8(
                    v___x_4533_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4519_,
                );
                lean_ctor_set_uint8(
                    v___x_4533_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4520_,
                );
                v___x_4534_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_a_4488_,
                    v___x_4527_,
                    v___x_4528_,
                    v___x_4533_,
                    v___y_4453_,
                    v___y_4454_,
                    v___y_4455_,
                );
                lean_dec_ref_known(v___x_4533_, 7);
                if lean_obj_tag(v___x_4534_) == 0 {
                    v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
                    lean_inc(v_a_4535_);
                    lean_dec_ref_known(v___x_4534_, 1);
                    v_snd_4536_ = lean_ctor_get(v_a_4535_, 1);
                    lean_inc(v_snd_4536_);
                    v_fst_4537_ = lean_ctor_get(v_a_4535_, 0);
                    lean_inc(v_fst_4537_);
                    lean_dec(v_a_4535_);
                    v_snd_4538_ = lean_ctor_get(v_snd_4536_, 1);
                    lean_inc(v_snd_4538_);
                    lean_dec(v_snd_4536_);
                    v___x_4539_ = l_Lean_instInhabitedExpr;
                    v___x_4540_ = lean_array_get_size(v_fst_4537_);
                    v___x_4541_ = lean_unsigned_to_nat(1);
                    v___x_4542_ = lean_nat_sub(v___x_4540_, v___x_4541_);
                    v___x_4543_ = lean_array_get_borrowed(v___x_4539_, v_fst_4537_, v___x_4542_);
                    lean_dec(v___x_4542_);
                    lean_inc_ref(v_e_4450_);
                    lean_inc(v___x_4543_);
                    v___x_4544_ = l_Lean_Meta_isExprDefEq(
                        v___x_4543_,
                        v_e_4450_,
                        v___y_4452_,
                        v___y_4453_,
                        v___y_4454_,
                        v___y_4455_,
                    );
                    if lean_obj_tag(v___x_4544_) == 0 {
                        v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
                        lean_inc(v_a_4545_);
                        lean_dec_ref_known(v___x_4544_, 1);
                        v___x_4546_ = (lean_unbox(v_a_4545_) as u8);
                        lean_dec(v_a_4545_);
                        if v___x_4546_ == 1 {
                            v___x_4547_ = l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg(v_snd_4538_, v___y_4453_);
                            v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
                            lean_inc(v_a_4548_);
                            lean_dec_ref(v___x_4547_);
                            v___x_4549_ = l_Lean_mkAppN(v_a_4486_, v_fst_4537_);
                            lean_dec(v_fst_4537_);
                            v___x_4550_ = l_Lean_Meta_mkExpectedTypeHint(
                                v___x_4549_,
                                v_a_4548_,
                                v___y_4452_,
                                v___y_4453_,
                                v___y_4454_,
                                v___y_4455_,
                            );
                            v___y_4482_ = v___x_4550_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_snd_4538_);
                            lean_dec(v_fst_4537_);
                            lean_dec(v_a_4486_);
                            v___x_4551_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1_once), _init_l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1);
                            v___x_4552_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4551_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
                            v___y_4482_ = v___x_4552_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4538_);
                        lean_dec(v_fst_4537_);
                        lean_dec(v_a_4486_);
                        v_a_4553_ = lean_ctor_get(v___x_4544_, 0);
                        v_isSharedCheck_4560_ = (!lean_is_exclusive(v___x_4544_)) as u8;
                        if v_isSharedCheck_4560_ == 0 {
                            v___x_4555_ = v___x_4544_;
                            v_isShared_4556_ = v_isSharedCheck_4560_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4553_);
                            lean_dec(v___x_4544_);
                            v___x_4555_ = lean_box(0);
                            v_isShared_4556_ = v_isSharedCheck_4560_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4486_);
                    v_a_4561_ = lean_ctor_get(v___x_4534_, 0);
                    v_isSharedCheck_4568_ = (!lean_is_exclusive(v___x_4534_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4563_ = v___x_4534_;
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4561_);
                        lean_dec(v___x_4534_);
                        v___x_4563_ = lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                lean_inc(v_a_4553_);
                if v_isShared_4556_ == 0 {
                    v___x_4558_ = v___x_4555_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
                    v___x_4558_ = v_reuseFailAlloc_4559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_4477_ = v___x_4558_;
                v_a_4478_ = v_a_4553_;
                state = 4;
                continue;
            }
            10 => {
                lean_inc(v_a_4561_);
                if v_isShared_4564_ == 0 {
                    v___x_4566_ = v___x_4563_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
                    v___x_4566_ = v_reuseFailAlloc_4567_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_4477_ = v___x_4566_;
                v_a_4478_ = v_a_4561_;
                state = 4;
                continue;
            }
            12 => {
                lean_inc(v_a_4571_);
                if v_isShared_4574_ == 0 {
                    v___x_4576_ = v___x_4573_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
                    v___x_4576_ = v_reuseFailAlloc_4577_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_4477_ = v___x_4576_;
                v_a_4478_ = v_a_4571_;
                state = 4;
                continue;
            }
            14 => {
                if v_isShared_4582_ == 0 {
                    v___x_4584_ = v___x_4581_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
                    v___x_4584_ = v_reuseFailAlloc_4585_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_firstM___at___00Lean_Expr_applySymm_spec__1___boxed(
    mut v_a_4587_: *mut LeanObject,
    mut v_e_4588_: *mut LeanObject,
    mut v_x_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
    mut v___y_4594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4595_: *mut LeanObject = core::ptr::null_mut();
    v_res_4595_ = l_List_firstM___at___00Lean_Expr_applySymm_spec__1(
        v_a_4587_,
        v_e_4588_,
        v_x_4589_,
        v___y_4590_,
        v___y_4591_,
        v___y_4592_,
        v___y_4593_,
    );
    lean_dec(v___y_4593_);
    lean_dec_ref(v___y_4592_);
    lean_dec(v___y_4591_);
    lean_dec_ref(v___y_4590_);
    lean_dec_ref(v_a_4587_);
    return v_res_4595_;
}
pub unsafe fn _init_l_Lean_Expr_applySymm___closed__1() -> *mut LeanObject {
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    v___x_4597_ = l_Lean_Expr_applySymm___closed__0;
    v___x_4598_ = l_Lean_stringToMessageData(v___x_4597_);
    return v___x_4598_;
}
pub unsafe fn _init_l_Lean_Expr_applySymm___closed__3() -> *mut LeanObject {
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    v___x_4600_ = l_Lean_Expr_applySymm___closed__2;
    v___x_4601_ = l_Lean_stringToMessageData(v___x_4600_);
    return v___x_4601_;
}
pub unsafe fn _init_l_Lean_Expr_applySymm___closed__4() -> *mut LeanObject {
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    v___x_4602_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__3_once),
        _init_l_Lean_Expr_applySymm___closed__3,
    );
    v___x_4603_ = l_Lean_MessageData_note(v___x_4602_);
    return v___x_4603_;
}
pub unsafe fn l_Lean_Expr_applySymm(
    mut v_e_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
    mut v_a_4606_: *mut LeanObject,
    mut v_a_4607_: *mut LeanObject,
    mut v_a_4608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4624_: u8 = 0;
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4635_: u8 = 0;
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4639_: u8 = 0;
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: u8 = 0;
    let mut v_a_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4645_: u8 = 0;
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4649_: u8 = 0;
    let mut v_a_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v_a_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4661_: u8 = 0;
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_4608_);
                lean_inc_ref(v_a_4607_);
                lean_inc(v_a_4606_);
                lean_inc_ref(v_a_4605_);
                lean_inc_ref(v_e_4604_);
                v___x_4610_ =
                    lean_infer_type(v_e_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
                if lean_obj_tag(v___x_4610_) == 0 {
                    v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
                    lean_inc(v_a_4611_);
                    lean_dec_ref_known(v___x_4610_, 1);
                    v___x_4612_ =
                        l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg(
                            v_a_4611_, v_a_4606_,
                        );
                    v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
                    lean_inc_n(v_a_4613_, 2);
                    lean_dec_ref(v___x_4612_);
                    v___x_4614_ = l_Lean_Expr_getSymmLems(
                        v_a_4613_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_,
                    );
                    if lean_obj_tag(v___x_4614_) == 0 {
                        v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
                        lean_inc(v_a_4615_);
                        lean_dec_ref_known(v___x_4614_, 1);
                        v___x_4616_ = l_Lean_Meta_saveState___redArg(v_a_4606_, v_a_4608_);
                        if lean_obj_tag(v___x_4616_) == 0 {
                            v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
                            lean_inc(v_a_4617_);
                            lean_dec_ref_known(v___x_4616_, 1);
                            v___x_4618_ = l_Lean_Meta_saveState___redArg(v_a_4606_, v_a_4608_);
                            if lean_obj_tag(v___x_4618_) == 0 {
                                v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
                                lean_inc(v_a_4619_);
                                lean_dec_ref_known(v___x_4618_, 1);
                                v___x_4620_ = lean_array_to_list(v_a_4615_);
                                v___x_4621_ = l_List_firstM___at___00Lean_Expr_applySymm_spec__1(
                                    v_a_4617_,
                                    v_e_4604_,
                                    v___x_4620_,
                                    v_a_4605_,
                                    v_a_4606_,
                                    v_a_4607_,
                                    v_a_4608_,
                                );
                                lean_dec(v_a_4617_);
                                if lean_obj_tag(v___x_4621_) == 0 {
                                    lean_dec(v_a_4619_);
                                    lean_dec(v_a_4613_);
                                    return v___x_4621_;
                                } else {
                                    v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
                                    lean_inc(v_a_4622_);
                                    v___x_4640_ = l_Lean_Exception_isInterrupt(v_a_4622_);
                                    if v___x_4640_ == 0 {
                                        v___x_4641_ = l_Lean_Exception_isRuntime(v_a_4622_);
                                        v___y_4624_ = v___x_4641_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_a_4622_);
                                        v___y_4624_ = v___x_4640_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4617_);
                                lean_dec(v_a_4615_);
                                lean_dec(v_a_4613_);
                                lean_dec_ref(v_e_4604_);
                                v_a_4642_ = lean_ctor_get(v___x_4618_, 0);
                                v_isSharedCheck_4649_ = (!lean_is_exclusive(v___x_4618_)) as u8;
                                if v_isSharedCheck_4649_ == 0 {
                                    v___x_4644_ = v___x_4618_;
                                    v_isShared_4645_ = v_isSharedCheck_4649_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4642_);
                                    lean_dec(v___x_4618_);
                                    v___x_4644_ = lean_box(0);
                                    v_isShared_4645_ = v_isSharedCheck_4649_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4615_);
                            lean_dec(v_a_4613_);
                            lean_dec_ref(v_e_4604_);
                            v_a_4650_ = lean_ctor_get(v___x_4616_, 0);
                            v_isSharedCheck_4657_ = (!lean_is_exclusive(v___x_4616_)) as u8;
                            if v_isSharedCheck_4657_ == 0 {
                                v___x_4652_ = v___x_4616_;
                                v_isShared_4653_ = v_isSharedCheck_4657_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4650_);
                                lean_dec(v___x_4616_);
                                v___x_4652_ = lean_box(0);
                                v_isShared_4653_ = v_isSharedCheck_4657_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4613_);
                        lean_dec_ref(v_e_4604_);
                        v_a_4658_ = lean_ctor_get(v___x_4614_, 0);
                        v_isSharedCheck_4665_ = (!lean_is_exclusive(v___x_4614_)) as u8;
                        if v_isSharedCheck_4665_ == 0 {
                            v___x_4660_ = v___x_4614_;
                            v_isShared_4661_ = v_isSharedCheck_4665_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4658_);
                            lean_dec(v___x_4614_);
                            v___x_4660_ = lean_box(0);
                            v_isShared_4661_ = v_isSharedCheck_4665_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_4604_);
                    return v___x_4610_;
                }
            }
            1 => {
                if v___y_4624_ == 0 {
                    lean_dec_ref_known(v___x_4621_, 1);
                    v___x_4625_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_4619_, v_a_4606_, v_a_4608_);
                    lean_dec(v_a_4619_);
                    if lean_obj_tag(v___x_4625_) == 0 {
                        lean_dec_ref_known(v___x_4625_, 1);
                        v___x_4626_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__1_once),
                            _init_l_Lean_Expr_applySymm___closed__1,
                        );
                        v___x_4627_ = l_Lean_indentExpr(v_a_4613_);
                        v___x_4628_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4628_, 0, v___x_4626_);
                        lean_ctor_set(v___x_4628_, 1, v___x_4627_);
                        v___x_4629_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__4_once),
                            _init_l_Lean_Expr_applySymm___closed__4,
                        );
                        v___x_4630_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4630_, 0, v___x_4628_);
                        lean_ctor_set(v___x_4630_, 1, v___x_4629_);
                        v___x_4631_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4630_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
                        return v___x_4631_;
                    } else {
                        lean_dec(v_a_4613_);
                        v_a_4632_ = lean_ctor_get(v___x_4625_, 0);
                        v_isSharedCheck_4639_ = (!lean_is_exclusive(v___x_4625_)) as u8;
                        if v_isSharedCheck_4639_ == 0 {
                            v___x_4634_ = v___x_4625_;
                            v_isShared_4635_ = v_isSharedCheck_4639_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4632_);
                            lean_dec(v___x_4625_);
                            v___x_4634_ = lean_box(0);
                            v_isShared_4635_ = v_isSharedCheck_4639_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4619_);
                    lean_dec(v_a_4613_);
                    return v___x_4621_;
                }
            }
            2 => {
                if v_isShared_4635_ == 0 {
                    v___x_4637_ = v___x_4634_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
                    v___x_4637_ = v_reuseFailAlloc_4638_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4637_;
            }
            4 => {
                if v_isShared_4645_ == 0 {
                    v___x_4647_ = v___x_4644_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
                    v___x_4647_ = v_reuseFailAlloc_4648_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4647_;
            }
            6 => {
                if v_isShared_4653_ == 0 {
                    v___x_4655_ = v___x_4652_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
                    v___x_4655_ = v_reuseFailAlloc_4656_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4655_;
            }
            8 => {
                if v_isShared_4661_ == 0 {
                    v___x_4663_ = v___x_4660_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
                    v___x_4663_ = v_reuseFailAlloc_4664_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_applySymm___boxed(
    mut v_e_4666_: *mut LeanObject,
    mut v_a_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
    mut v_a_4669_: *mut LeanObject,
    mut v_a_4670_: *mut LeanObject,
    mut v_a_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4672_: *mut LeanObject = core::ptr::null_mut();
    v_res_4672_ = l_Lean_Expr_applySymm(v_e_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
    lean_dec(v_a_4670_);
    lean_dec_ref(v_a_4669_);
    lean_dec(v_a_4668_);
    lean_dec_ref(v_a_4667_);
    return v_res_4672_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(
    mut v_x_4673_: *mut LeanObject,
    mut v_x_4674_: *mut LeanObject,
    mut v_x_4675_: *mut LeanObject,
    mut v_x_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: u8 = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4677_ = lean_ctor_get(v_x_4673_, 0);
                v_vs_4678_ = lean_ctor_get(v_x_4673_, 1);
                v_isSharedCheck_4702_ = (!lean_is_exclusive(v_x_4673_)) as u8;
                if v_isSharedCheck_4702_ == 0 {
                    v___x_4680_ = v_x_4673_;
                    v_isShared_4681_ = v_isSharedCheck_4702_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4678_);
                    lean_inc(v_ks_4677_);
                    lean_dec(v_x_4673_);
                    v___x_4680_ = lean_box(0);
                    v_isShared_4681_ = v_isSharedCheck_4702_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4682_ = lean_array_get_size(v_ks_4677_);
                v___x_4683_ = lean_nat_dec_lt(v_x_4674_, v___x_4682_);
                if v___x_4683_ == 0 {
                    lean_dec(v_x_4674_);
                    v___x_4684_ = lean_array_push(v_ks_4677_, v_x_4675_);
                    v___x_4685_ = lean_array_push(v_vs_4678_, v_x_4676_);
                    if v_isShared_4681_ == 0 {
                        lean_ctor_set(v___x_4680_, 1, v___x_4685_);
                        lean_ctor_set(v___x_4680_, 0, v___x_4684_);
                        v___x_4687_ = v___x_4680_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4684_);
                        lean_ctor_set(v_reuseFailAlloc_4688_, 1, v___x_4685_);
                        v___x_4687_ = v_reuseFailAlloc_4688_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4689_ = lean_array_fget_borrowed(v_ks_4677_, v_x_4674_);
                    v___x_4690_ = l_Lean_instBEqMVarId_beq(v_x_4675_, v_k_x27_4689_);
                    if v___x_4690_ == 0 {
                        if v_isShared_4681_ == 0 {
                            v___x_4692_ = v___x_4680_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_ks_4677_);
                            lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_vs_4678_);
                            v___x_4692_ = v_reuseFailAlloc_4696_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4697_ = lean_array_fset(v_ks_4677_, v_x_4674_, v_x_4675_);
                        v___x_4698_ = lean_array_fset(v_vs_4678_, v_x_4674_, v_x_4676_);
                        lean_dec(v_x_4674_);
                        if v_isShared_4681_ == 0 {
                            lean_ctor_set(v___x_4680_, 1, v___x_4698_);
                            lean_ctor_set(v___x_4680_, 0, v___x_4697_);
                            v___x_4700_ = v___x_4680_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4697_);
                            lean_ctor_set(v_reuseFailAlloc_4701_, 1, v___x_4698_);
                            v___x_4700_ = v_reuseFailAlloc_4701_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4687_;
            }
            3 => {
                v___x_4693_ = lean_unsigned_to_nat(1);
                v___x_4694_ = lean_nat_add(v_x_4674_, v___x_4693_);
                lean_dec(v_x_4674_);
                v_x_4673_ = v___x_4692_;
                v_x_4674_ = v___x_4694_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_n_4703_: *mut LeanObject,
    mut v_k_4704_: *mut LeanObject,
    mut v_v_4705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    v___x_4706_ = lean_unsigned_to_nat(0);
    v___x_4707_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_4703_, v___x_4706_, v_k_4704_, v_v_4705_);
    return v___x_4707_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    v___x_4708_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4708_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg(
    mut v_x_4709_: *mut LeanObject,
    mut v_x_4710_: usize,
    mut v_x_4711_: usize,
    mut v_x_4712_: *mut LeanObject,
    mut v_x_4713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: usize = 0;
    let mut v___x_4716_: usize = 0;
    let mut v___x_4717_: usize = 0;
    let mut v___x_4718_: usize = 0;
    let mut v_j_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4724_: u8 = 0;
    let mut v_v_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut v_node_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4756_: u8 = 0;
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut v_unused_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4769_: u8 = 0;
    let mut v_ks_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: usize = 0;
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: u8 = 0;
    let mut v_reuseFailAlloc_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4709_) == 0 {
                    v_es_4714_ = lean_ctor_get(v_x_4709_, 0);
                    v___x_4715_ = 5usize;
                    v___x_4716_ = 1usize;
                    v___x_4717_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4718_ = lean_usize_land(v_x_4710_, v___x_4717_);
                    v_j_4719_ = lean_usize_to_nat(v___x_4718_);
                    v___x_4720_ = lean_array_get_size(v_es_4714_);
                    v___x_4721_ = lean_nat_dec_lt(v_j_4719_, v___x_4720_);
                    if v___x_4721_ == 0 {
                        lean_dec(v_j_4719_);
                        lean_dec(v_x_4713_);
                        lean_dec(v_x_4712_);
                        return v_x_4709_;
                    } else {
                        lean_inc_ref(v_es_4714_);
                        v_isSharedCheck_4758_ = (!lean_is_exclusive(v_x_4709_)) as u8;
                        if v_isSharedCheck_4758_ == 0 {
                            v_unused_4759_ = lean_ctor_get(v_x_4709_, 0);
                            lean_dec(v_unused_4759_);
                            v___x_4723_ = v_x_4709_;
                            v_isShared_4724_ = v_isSharedCheck_4758_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4709_);
                            v___x_4723_ = lean_box(0);
                            v_isShared_4724_ = v_isSharedCheck_4758_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4760_ = lean_ctor_get(v_x_4709_, 0);
                    v_vs_4761_ = lean_ctor_get(v_x_4709_, 1);
                    v_isSharedCheck_4781_ = (!lean_is_exclusive(v_x_4709_)) as u8;
                    if v_isSharedCheck_4781_ == 0 {
                        v___x_4763_ = v_x_4709_;
                        v_isShared_4764_ = v_isSharedCheck_4781_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4761_);
                        lean_inc(v_ks_4760_);
                        lean_dec(v_x_4709_);
                        v___x_4763_ = lean_box(0);
                        v_isShared_4764_ = v_isSharedCheck_4781_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4725_ = lean_array_fget(v_es_4714_, v_j_4719_);
                v___x_4726_ = lean_box(0);
                v_xs_x27_4727_ = lean_array_fset(v_es_4714_, v_j_4719_, v___x_4726_);
                match lean_obj_tag(v_v_4725_) {
                    0 => {
                        v_key_4734_ = lean_ctor_get(v_v_4725_, 0);
                        v_val_4735_ = lean_ctor_get(v_v_4725_, 1);
                        v_isSharedCheck_4745_ = (!lean_is_exclusive(v_v_4725_)) as u8;
                        if v_isSharedCheck_4745_ == 0 {
                            v___x_4737_ = v_v_4725_;
                            v_isShared_4738_ = v_isSharedCheck_4745_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4735_);
                            lean_inc(v_key_4734_);
                            lean_dec(v_v_4725_);
                            v___x_4737_ = lean_box(0);
                            v_isShared_4738_ = v_isSharedCheck_4745_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4746_ = lean_ctor_get(v_v_4725_, 0);
                        v_isSharedCheck_4756_ = (!lean_is_exclusive(v_v_4725_)) as u8;
                        if v_isSharedCheck_4756_ == 0 {
                            v___x_4748_ = v_v_4725_;
                            v_isShared_4749_ = v_isSharedCheck_4756_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4746_);
                            lean_dec(v_v_4725_);
                            v___x_4748_ = lean_box(0);
                            v_isShared_4749_ = v_isSharedCheck_4756_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4757_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4757_, 0, v_x_4712_);
                        lean_ctor_set(v___x_4757_, 1, v_x_4713_);
                        v___y_4729_ = v___x_4757_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4730_ = lean_array_fset(v_xs_x27_4727_, v_j_4719_, v___y_4729_);
                lean_dec(v_j_4719_);
                if v_isShared_4724_ == 0 {
                    lean_ctor_set(v___x_4723_, 0, v___x_4730_);
                    v___x_4732_ = v___x_4723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4730_);
                    v___x_4732_ = v_reuseFailAlloc_4733_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4732_;
            }
            4 => {
                v___x_4739_ = l_Lean_instBEqMVarId_beq(v_x_4712_, v_key_4734_);
                if v___x_4739_ == 0 {
                    lean_del_object(v___x_4737_);
                    v___x_4740_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4734_,
                        v_val_4735_,
                        v_x_4712_,
                        v_x_4713_,
                    );
                    v___x_4741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4741_, 0, v___x_4740_);
                    v___y_4729_ = v___x_4741_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4735_);
                    lean_dec(v_key_4734_);
                    if v_isShared_4738_ == 0 {
                        lean_ctor_set(v___x_4737_, 1, v_x_4713_);
                        lean_ctor_set(v___x_4737_, 0, v_x_4712_);
                        v___x_4743_ = v___x_4737_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_x_4712_);
                        lean_ctor_set(v_reuseFailAlloc_4744_, 1, v_x_4713_);
                        v___x_4743_ = v_reuseFailAlloc_4744_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4729_ = v___x_4743_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4750_ = lean_usize_shift_right(v_x_4710_, v___x_4715_);
                v___x_4751_ = lean_usize_add(v_x_4711_, v___x_4716_);
                v___x_4752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg(v_node_4746_, v___x_4750_, v___x_4751_, v_x_4712_, v_x_4713_);
                if v_isShared_4749_ == 0 {
                    lean_ctor_set(v___x_4748_, 0, v___x_4752_);
                    v___x_4754_ = v___x_4748_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4752_);
                    v___x_4754_ = v_reuseFailAlloc_4755_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4729_ = v___x_4754_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4764_ == 0 {
                    v___x_4766_ = v___x_4763_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_ks_4760_);
                    lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_vs_4761_);
                    v___x_4766_ = v_reuseFailAlloc_4780_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4766_, v_x_4712_, v_x_4713_);
                v___x_4775_ = 7usize;
                v___x_4776_ = lean_usize_dec_le(v___x_4775_, v_x_4711_);
                if v___x_4776_ == 0 {
                    v___x_4777_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4767_);
                    v___x_4778_ = lean_unsigned_to_nat(4);
                    v___x_4779_ = lean_nat_dec_lt(v___x_4777_, v___x_4778_);
                    lean_dec(v___x_4777_);
                    v___y_4769_ = v___x_4779_;
                    state = 10;
                    continue;
                } else {
                    v___y_4769_ = v___x_4776_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4769_ == 0 {
                    v_ks_4770_ = lean_ctor_get(v_newNode_4767_, 0);
                    lean_inc_ref(v_ks_4770_);
                    v_vs_4771_ = lean_ctor_get(v_newNode_4767_, 1);
                    lean_inc_ref(v_vs_4771_);
                    lean_dec_ref(v_newNode_4767_);
                    v___x_4772_ = lean_unsigned_to_nat(0);
                    v___x_4773_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___closed__0);
                    v___x_4774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4711_, v_ks_4770_, v_vs_4771_, v___x_4772_, v___x_4773_);
                    lean_dec_ref(v_vs_4771_);
                    lean_dec_ref(v_ks_4770_);
                    return v___x_4774_;
                } else {
                    return v_newNode_4767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_depth_4782_: usize,
    mut v_keys_4783_: *mut LeanObject,
    mut v_vals_4784_: *mut LeanObject,
    mut v_i_4785_: *mut LeanObject,
    mut v_entries_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: u8 = 0;
    let mut v_k_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u64 = 0;
    let mut v_h_4792_: usize = 0;
    let mut v___x_4793_: usize = 0;
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v___x_4797_: usize = 0;
    let mut v_h_4798_: usize = 0;
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4787_ = lean_array_get_size(v_keys_4783_);
                v___x_4788_ = lean_nat_dec_lt(v_i_4785_, v___x_4787_);
                if v___x_4788_ == 0 {
                    lean_dec(v_i_4785_);
                    return v_entries_4786_;
                } else {
                    v_k_4789_ = lean_array_fget_borrowed(v_keys_4783_, v_i_4785_);
                    v_v_4790_ = lean_array_fget_borrowed(v_vals_4784_, v_i_4785_);
                    v___x_4791_ = l_Lean_instHashableMVarId_hash(v_k_4789_);
                    v_h_4792_ = lean_uint64_to_usize(v___x_4791_);
                    v___x_4793_ = 5usize;
                    v___x_4794_ = lean_unsigned_to_nat(1);
                    v___x_4795_ = 1usize;
                    v___x_4796_ = lean_usize_sub(v_depth_4782_, v___x_4795_);
                    v___x_4797_ = lean_usize_mul(v___x_4793_, v___x_4796_);
                    v_h_4798_ = lean_usize_shift_right(v_h_4792_, v___x_4797_);
                    v___x_4799_ = lean_nat_add(v_i_4785_, v___x_4794_);
                    lean_dec(v_i_4785_);
                    lean_inc(v_v_4790_);
                    lean_inc(v_k_4789_);
                    v___x_4800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg(v_entries_4786_, v_h_4798_, v_depth_4782_, v_k_4789_, v_v_4790_);
                    v_i_4785_ = v___x_4799_;
                    v_entries_4786_ = v___x_4800_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_depth_4802_: *mut LeanObject,
    mut v_keys_4803_: *mut LeanObject,
    mut v_vals_4804_: *mut LeanObject,
    mut v_i_4805_: *mut LeanObject,
    mut v_entries_4806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4807_: usize = 0;
    let mut v_res_4808_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4807_ = lean_unbox_usize(v_depth_4802_);
    lean_dec(v_depth_4802_);
    v_res_4808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4807_, v_keys_4803_, v_vals_4804_, v_i_4805_, v_entries_4806_);
    lean_dec_ref(v_vals_4804_);
    lean_dec_ref(v_keys_4803_);
    return v_res_4808_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4809_: *mut LeanObject,
    mut v_x_4810_: *mut LeanObject,
    mut v_x_4811_: *mut LeanObject,
    mut v_x_4812_: *mut LeanObject,
    mut v_x_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3860__boxed_4814_: usize = 0;
    let mut v_x_3861__boxed_4815_: usize = 0;
    let mut v_res_4816_: *mut LeanObject = core::ptr::null_mut();
    v_x_3860__boxed_4814_ = lean_unbox_usize(v_x_4810_);
    lean_dec(v_x_4810_);
    v_x_3861__boxed_4815_ = lean_unbox_usize(v_x_4811_);
    lean_dec(v_x_4811_);
    v_res_4816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg(v_x_4809_, v_x_3860__boxed_4814_, v_x_3861__boxed_4815_, v_x_4812_, v_x_4813_);
    return v_res_4816_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0___redArg(
    mut v_x_4817_: *mut LeanObject,
    mut v_x_4818_: *mut LeanObject,
    mut v_x_4819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4820_: u64 = 0;
    let mut v___x_4821_: usize = 0;
    let mut v___x_4822_: usize = 0;
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    v___x_4820_ = l_Lean_instHashableMVarId_hash(v_x_4818_);
    v___x_4821_ = lean_uint64_to_usize(v___x_4820_);
    v___x_4822_ = 1usize;
    v___x_4823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg(v_x_4817_, v___x_4821_, v___x_4822_, v_x_4818_, v_x_4819_);
    return v___x_4823_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0___redArg(
    mut v_mvarId_4824_: *mut LeanObject,
    mut v_val_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v_depth_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4849_: u8 = 0;
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4828_ = lean_st_ref_take(v___y_4826_);
                v_mctx_4829_ = lean_ctor_get(v___x_4828_, 0);
                v_cache_4830_ = lean_ctor_get(v___x_4828_, 1);
                v_zetaDeltaFVarIds_4831_ = lean_ctor_get(v___x_4828_, 2);
                v_postponed_4832_ = lean_ctor_get(v___x_4828_, 3);
                v_diag_4833_ = lean_ctor_get(v___x_4828_, 4);
                v_isSharedCheck_4861_ = (!lean_is_exclusive(v___x_4828_)) as u8;
                if v_isSharedCheck_4861_ == 0 {
                    v___x_4835_ = v___x_4828_;
                    v_isShared_4836_ = v_isSharedCheck_4861_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_4833_);
                    lean_inc(v_postponed_4832_);
                    lean_inc(v_zetaDeltaFVarIds_4831_);
                    lean_inc(v_cache_4830_);
                    lean_inc(v_mctx_4829_);
                    lean_dec(v___x_4828_);
                    v___x_4835_ = lean_box(0);
                    v_isShared_4836_ = v_isSharedCheck_4861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4837_ = lean_ctor_get(v_mctx_4829_, 0);
                v_levelAssignDepth_4838_ = lean_ctor_get(v_mctx_4829_, 1);
                v_lmvarCounter_4839_ = lean_ctor_get(v_mctx_4829_, 2);
                v_mvarCounter_4840_ = lean_ctor_get(v_mctx_4829_, 3);
                v_lDecls_4841_ = lean_ctor_get(v_mctx_4829_, 4);
                v_decls_4842_ = lean_ctor_get(v_mctx_4829_, 5);
                v_userNames_4843_ = lean_ctor_get(v_mctx_4829_, 6);
                v_lAssignment_4844_ = lean_ctor_get(v_mctx_4829_, 7);
                v_eAssignment_4845_ = lean_ctor_get(v_mctx_4829_, 8);
                v_dAssignment_4846_ = lean_ctor_get(v_mctx_4829_, 9);
                v_isSharedCheck_4860_ = (!lean_is_exclusive(v_mctx_4829_)) as u8;
                if v_isSharedCheck_4860_ == 0 {
                    v___x_4848_ = v_mctx_4829_;
                    v_isShared_4849_ = v_isSharedCheck_4860_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_4846_);
                    lean_inc(v_eAssignment_4845_);
                    lean_inc(v_lAssignment_4844_);
                    lean_inc(v_userNames_4843_);
                    lean_inc(v_decls_4842_);
                    lean_inc(v_lDecls_4841_);
                    lean_inc(v_mvarCounter_4840_);
                    lean_inc(v_lmvarCounter_4839_);
                    lean_inc(v_levelAssignDepth_4838_);
                    lean_inc(v_depth_4837_);
                    lean_dec(v_mctx_4829_);
                    v___x_4848_ = lean_box(0);
                    v_isShared_4849_ = v_isSharedCheck_4860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4850_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0___redArg(v_eAssignment_4845_, v_mvarId_4824_, v_val_4825_);
                if v_isShared_4849_ == 0 {
                    lean_ctor_set(v___x_4848_, 8, v___x_4850_);
                    v___x_4852_ = v___x_4848_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_depth_4837_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 1, v_levelAssignDepth_4838_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 2, v_lmvarCounter_4839_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 3, v_mvarCounter_4840_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 4, v_lDecls_4841_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 5, v_decls_4842_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 6, v_userNames_4843_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 7, v_lAssignment_4844_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 8, v___x_4850_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 9, v_dAssignment_4846_);
                    v___x_4852_ = v_reuseFailAlloc_4859_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4836_ == 0 {
                    lean_ctor_set(v___x_4835_, 0, v___x_4852_);
                    v___x_4854_ = v___x_4835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4852_);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_cache_4830_);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_zetaDeltaFVarIds_4831_);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 3, v_postponed_4832_);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 4, v_diag_4833_);
                    v___x_4854_ = v_reuseFailAlloc_4858_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4855_ = lean_st_ref_set(v___y_4826_, v___x_4854_);
                v___x_4856_ = lean_box(0);
                v___x_4857_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4857_, 0, v___x_4856_);
                return v___x_4857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0___redArg___boxed(
    mut v_mvarId_4862_: *mut LeanObject,
    mut v_val_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
    mut v___y_4865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4866_: *mut LeanObject = core::ptr::null_mut();
    v_res_4866_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0___redArg(
        v_mvarId_4862_,
        v_val_4863_,
        v___y_4864_,
    );
    lean_dec(v___y_4864_);
    return v_res_4866_;
}
pub unsafe fn l_List_firstM___at___00Lean_MVarId_applySymm_spec__1(
    mut v_g_4867_: *mut LeanObject,
    mut v_x_4868_: *mut LeanObject,
    mut v___y_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4882_: u8 = 0;
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut v___y_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: u8 = 0;
    let mut v___x_4897_: u8 = 0;
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4903_: u8 = 0;
    let mut v_ctxApprox_4904_: u8 = 0;
    let mut v_quasiPatternApprox_4905_: u8 = 0;
    let mut v_constApprox_4906_: u8 = 0;
    let mut v_isDefEqStuckEx_4907_: u8 = 0;
    let mut v_unificationHints_4908_: u8 = 0;
    let mut v_proofIrrelevance_4909_: u8 = 0;
    let mut v_assignSyntheticOpaque_4910_: u8 = 0;
    let mut v_offsetCnstrs_4911_: u8 = 0;
    let mut v_etaStruct_4912_: u8 = 0;
    let mut v_univApprox_4913_: u8 = 0;
    let mut v_iota_4914_: u8 = 0;
    let mut v_beta_4915_: u8 = 0;
    let mut v_proj_4916_: u8 = 0;
    let mut v_zeta_4917_: u8 = 0;
    let mut v_zetaDelta_4918_: u8 = 0;
    let mut v_zetaUnused_4919_: u8 = 0;
    let mut v_zetaHave_4920_: u8 = 0;
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v_trackZetaDelta_4924_: u8 = 0;
    let mut v_zetaDeltaSet_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4931_: u8 = 0;
    let mut v_inTypeClassResolution_4932_: u8 = 0;
    let mut v_cacheInferType_4933_: u8 = 0;
    let mut v___x_4934_: u8 = 0;
    let mut v_config_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u64 = 0;
    let mut v___x_4938_: u64 = 0;
    let mut v___x_4939_: u64 = 0;
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: u8 = 0;
    let mut v___x_4942_: u64 = 0;
    let mut v___x_4943_: u64 = 0;
    let mut v_key_4944_: u64 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4970_: u8 = 0;
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4974_: u8 = 0;
    let mut v_unused_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut v_a_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4987_: u8 = 0;
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5002_: u8 = 0;
    let mut v_a_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_a_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5014_: u8 = 0;
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5018_: u8 = 0;
    let mut v_reuseFailAlloc_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut v_a_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5024_: u8 = 0;
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4868_) == 0 {
                    lean_dec(v_g_4867_);
                    v___x_4874_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1_once
                        ),
                        _init_l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1,
                    );
                    v___x_4875_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4874_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
                    return v___x_4875_;
                } else {
                    v_head_4876_ = lean_ctor_get(v_x_4868_, 0);
                    lean_inc(v_head_4876_);
                    v_tail_4877_ = lean_ctor_get(v_x_4868_, 1);
                    lean_inc(v_tail_4877_);
                    lean_dec_ref_known(v_x_4868_, 2);
                    v___x_4878_ = l_Lean_Meta_saveState___redArg(v___y_4870_, v___y_4872_);
                    if lean_obj_tag(v___x_4878_) == 0 {
                        v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
                        lean_inc(v_a_4879_);
                        lean_dec_ref_known(v___x_4878_, 1);
                        v___x_4898_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                            v_head_4876_,
                            v___y_4869_,
                            v___y_4870_,
                            v___y_4871_,
                            v___y_4872_,
                        );
                        if lean_obj_tag(v___x_4898_) == 0 {
                            v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
                            lean_inc_n(v_a_4899_, 2);
                            lean_dec_ref_known(v___x_4898_, 1);
                            lean_inc(v___y_4872_);
                            lean_inc_ref(v___y_4871_);
                            lean_inc(v___y_4870_);
                            lean_inc_ref(v___y_4869_);
                            v___x_4900_ = lean_infer_type(
                                v_a_4899_,
                                v___y_4869_,
                                v___y_4870_,
                                v___y_4871_,
                                v___y_4872_,
                            );
                            if lean_obj_tag(v___x_4900_) == 0 {
                                v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
                                lean_inc(v_a_4901_);
                                lean_dec_ref_known(v___x_4900_, 1);
                                v___x_4902_ = l_Lean_Meta_Context_config(v___y_4869_);
                                v_foApprox_4903_ = lean_ctor_get_uint8(v___x_4902_, 0 as u32);
                                v_ctxApprox_4904_ = lean_ctor_get_uint8(v___x_4902_, 1 as u32);
                                v_quasiPatternApprox_4905_ =
                                    lean_ctor_get_uint8(v___x_4902_, 2 as u32);
                                v_constApprox_4906_ = lean_ctor_get_uint8(v___x_4902_, 3 as u32);
                                v_isDefEqStuckEx_4907_ = lean_ctor_get_uint8(v___x_4902_, 4 as u32);
                                v_unificationHints_4908_ =
                                    lean_ctor_get_uint8(v___x_4902_, 5 as u32);
                                v_proofIrrelevance_4909_ =
                                    lean_ctor_get_uint8(v___x_4902_, 6 as u32);
                                v_assignSyntheticOpaque_4910_ =
                                    lean_ctor_get_uint8(v___x_4902_, 7 as u32);
                                v_offsetCnstrs_4911_ = lean_ctor_get_uint8(v___x_4902_, 8 as u32);
                                v_etaStruct_4912_ = lean_ctor_get_uint8(v___x_4902_, 10 as u32);
                                v_univApprox_4913_ = lean_ctor_get_uint8(v___x_4902_, 11 as u32);
                                v_iota_4914_ = lean_ctor_get_uint8(v___x_4902_, 12 as u32);
                                v_beta_4915_ = lean_ctor_get_uint8(v___x_4902_, 13 as u32);
                                v_proj_4916_ = lean_ctor_get_uint8(v___x_4902_, 14 as u32);
                                v_zeta_4917_ = lean_ctor_get_uint8(v___x_4902_, 15 as u32);
                                v_zetaDelta_4918_ = lean_ctor_get_uint8(v___x_4902_, 16 as u32);
                                v_zetaUnused_4919_ = lean_ctor_get_uint8(v___x_4902_, 17 as u32);
                                v_zetaHave_4920_ = lean_ctor_get_uint8(v___x_4902_, 18 as u32);
                                v_isSharedCheck_5020_ = (!lean_is_exclusive(v___x_4902_)) as u8;
                                if v_isSharedCheck_5020_ == 0 {
                                    v___x_4922_ = v___x_4902_;
                                    v_isShared_4923_ = v_isSharedCheck_5020_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v___x_4902_);
                                    v___x_4922_ = lean_box(0);
                                    v_isShared_4923_ = v_isSharedCheck_5020_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4899_);
                                v_a_5021_ = lean_ctor_get(v___x_4900_, 0);
                                v_isSharedCheck_5028_ = (!lean_is_exclusive(v___x_4900_)) as u8;
                                if v_isSharedCheck_5028_ == 0 {
                                    v___x_5023_ = v___x_4900_;
                                    v_isShared_5024_ = v_isSharedCheck_5028_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_5021_);
                                    lean_dec(v___x_4900_);
                                    v___x_5023_ = lean_box(0);
                                    v_isShared_5024_ = v_isSharedCheck_5028_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            v_a_5029_ = lean_ctor_get(v___x_4898_, 0);
                            v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_4898_)) as u8;
                            if v_isSharedCheck_5036_ == 0 {
                                v___x_5031_ = v___x_4898_;
                                v_isShared_5032_ = v_isSharedCheck_5036_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_5029_);
                                lean_dec(v___x_4898_);
                                v___x_5031_ = lean_box(0);
                                v_isShared_5032_ = v_isSharedCheck_5036_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_tail_4877_);
                        lean_dec(v_head_4876_);
                        lean_dec(v_g_4867_);
                        v_a_5037_ = lean_ctor_get(v___x_4878_, 0);
                        v_isSharedCheck_5044_ = (!lean_is_exclusive(v___x_4878_)) as u8;
                        if v_isSharedCheck_5044_ == 0 {
                            v___x_5039_ = v___x_4878_;
                            v_isShared_5040_ = v_isSharedCheck_5044_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_5037_);
                            lean_dec(v___x_4878_);
                            v___x_5039_ = lean_box(0);
                            v_isShared_5040_ = v_isSharedCheck_5044_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_4882_ == 0 {
                    lean_dec_ref(v___y_4881_);
                    v___x_4883_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_4879_,
                        v___y_4870_,
                        v___y_4872_,
                    );
                    lean_dec(v_a_4879_);
                    if lean_obj_tag(v___x_4883_) == 0 {
                        lean_dec_ref_known(v___x_4883_, 1);
                        v_x_4868_ = v_tail_4877_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_4877_);
                        lean_dec(v_g_4867_);
                        v_a_4885_ = lean_ctor_get(v___x_4883_, 0);
                        v_isSharedCheck_4892_ = (!lean_is_exclusive(v___x_4883_)) as u8;
                        if v_isSharedCheck_4892_ == 0 {
                            v___x_4887_ = v___x_4883_;
                            v_isShared_4888_ = v_isSharedCheck_4892_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4885_);
                            lean_dec(v___x_4883_);
                            v___x_4887_ = lean_box(0);
                            v_isShared_4888_ = v_isSharedCheck_4892_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4879_);
                    lean_dec(v_tail_4877_);
                    lean_dec(v_g_4867_);
                    return v___y_4881_;
                }
            }
            2 => {
                if v_isShared_4888_ == 0 {
                    v___x_4890_ = v___x_4887_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
                    v___x_4890_ = v_reuseFailAlloc_4891_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4890_;
            }
            4 => {
                v___x_4896_ = l_Lean_Exception_isInterrupt(v_a_4895_);
                if v___x_4896_ == 0 {
                    v___x_4897_ = l_Lean_Exception_isRuntime(v_a_4895_);
                    v___y_4881_ = v___y_4894_;
                    v___y_4882_ = v___x_4897_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_a_4895_);
                    v___y_4881_ = v___y_4894_;
                    v___y_4882_ = v___x_4896_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v_trackZetaDelta_4924_ = lean_ctor_get_uint8(
                    v___y_4869_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4925_ = lean_ctor_get(v___y_4869_, 1);
                v_lctx_4926_ = lean_ctor_get(v___y_4869_, 2);
                v_localInstances_4927_ = lean_ctor_get(v___y_4869_, 3);
                v_defEqCtx_x3f_4928_ = lean_ctor_get(v___y_4869_, 4);
                v_synthPendingDepth_4929_ = lean_ctor_get(v___y_4869_, 5);
                v_canUnfold_x3f_4930_ = lean_ctor_get(v___y_4869_, 6);
                v_univApprox_4931_ = lean_ctor_get_uint8(
                    v___y_4869_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4932_ = lean_ctor_get_uint8(
                    v___y_4869_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4933_ = lean_ctor_get_uint8(
                    v___y_4869_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_4934_ = 2;
                if v_isShared_4923_ == 0 {
                    v_config_4936_ = v___x_4922_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 0 as u32, v_foApprox_4903_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 1 as u32, v_ctxApprox_4904_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5019_,
                        2 as u32,
                        v_quasiPatternApprox_4905_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 3 as u32, v_constApprox_4906_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 4 as u32, v_isDefEqStuckEx_4907_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 5 as u32, v_unificationHints_4908_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 6 as u32, v_proofIrrelevance_4909_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5019_,
                        7 as u32,
                        v_assignSyntheticOpaque_4910_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 8 as u32, v_offsetCnstrs_4911_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 10 as u32, v_etaStruct_4912_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 11 as u32, v_univApprox_4913_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 12 as u32, v_iota_4914_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 13 as u32, v_beta_4915_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 14 as u32, v_proj_4916_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 15 as u32, v_zeta_4917_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 16 as u32, v_zetaDelta_4918_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 17 as u32, v_zetaUnused_4919_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5019_, 18 as u32, v_zetaHave_4920_);
                    v_config_4936_ = v_reuseFailAlloc_5019_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_ctor_set_uint8(v_config_4936_, 9 as u32, v___x_4934_);
                v___x_4937_ = l_Lean_Meta_Context_configKey(v___y_4869_);
                v___x_4938_ = 3u64;
                v___x_4939_ = lean_uint64_shift_right(v___x_4937_, v___x_4938_);
                v___x_4940_ = lean_box(0);
                v___x_4941_ = 0;
                v___x_4942_ = lean_uint64_shift_left(v___x_4939_, v___x_4938_);
                v___x_4943_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_);
                v_key_4944_ = lean_uint64_lor(v___x_4942_, v___x_4943_);
                v___x_4945_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4945_, 0, v_config_4936_);
                lean_ctor_set_uint64(
                    v___x_4945_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4944_,
                );
                lean_inc(v_canUnfold_x3f_4930_);
                lean_inc(v_synthPendingDepth_4929_);
                lean_inc(v_defEqCtx_x3f_4928_);
                lean_inc_ref(v_localInstances_4927_);
                lean_inc_ref(v_lctx_4926_);
                lean_inc(v_zetaDeltaSet_4925_);
                v___x_4946_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4946_, 0, v___x_4945_);
                lean_ctor_set(v___x_4946_, 1, v_zetaDeltaSet_4925_);
                lean_ctor_set(v___x_4946_, 2, v_lctx_4926_);
                lean_ctor_set(v___x_4946_, 3, v_localInstances_4927_);
                lean_ctor_set(v___x_4946_, 4, v_defEqCtx_x3f_4928_);
                lean_ctor_set(v___x_4946_, 5, v_synthPendingDepth_4929_);
                lean_ctor_set(v___x_4946_, 6, v_canUnfold_x3f_4930_);
                lean_ctor_set_uint8(
                    v___x_4946_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4924_,
                );
                lean_ctor_set_uint8(
                    v___x_4946_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4931_,
                );
                lean_ctor_set_uint8(
                    v___x_4946_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4932_,
                );
                lean_ctor_set_uint8(
                    v___x_4946_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4933_,
                );
                v___x_4947_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_a_4901_,
                    v___x_4940_,
                    v___x_4941_,
                    v___x_4946_,
                    v___y_4870_,
                    v___y_4871_,
                    v___y_4872_,
                );
                lean_dec_ref_known(v___x_4946_, 7);
                if lean_obj_tag(v___x_4947_) == 0 {
                    v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
                    lean_inc(v_a_4948_);
                    lean_dec_ref_known(v___x_4947_, 1);
                    v_snd_4949_ = lean_ctor_get(v_a_4948_, 1);
                    lean_inc(v_snd_4949_);
                    v_fst_4950_ = lean_ctor_get(v_a_4948_, 0);
                    lean_inc(v_fst_4950_);
                    lean_dec(v_a_4948_);
                    v_snd_4951_ = lean_ctor_get(v_snd_4949_, 1);
                    lean_inc(v_snd_4951_);
                    lean_dec(v_snd_4949_);
                    lean_inc(v_g_4867_);
                    v___x_4952_ = l_Lean_MVarId_getType(
                        v_g_4867_,
                        v___y_4869_,
                        v___y_4870_,
                        v___y_4871_,
                        v___y_4872_,
                    );
                    if lean_obj_tag(v___x_4952_) == 0 {
                        v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
                        lean_inc(v_a_4953_);
                        lean_dec_ref_known(v___x_4952_, 1);
                        v___x_4954_ = l_Lean_Meta_isExprDefEq(
                            v_a_4953_,
                            v_snd_4951_,
                            v___y_4869_,
                            v___y_4870_,
                            v___y_4871_,
                            v___y_4872_,
                        );
                        if lean_obj_tag(v___x_4954_) == 0 {
                            v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
                            lean_inc(v_a_4955_);
                            lean_dec_ref_known(v___x_4954_, 1);
                            v___x_4956_ = (lean_unbox(v_a_4955_) as u8);
                            lean_dec(v_a_4955_);
                            if v___x_4956_ == 1 {
                                v___x_4957_ = l_Lean_mkAppN(v_a_4899_, v_fst_4950_);
                                lean_inc_n(v_g_4867_, 2);
                                v___x_4958_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0___redArg(v_g_4867_, v___x_4957_, v___y_4870_);
                                lean_dec_ref(v___x_4958_);
                                v___x_4959_ = l_Lean_MVarId_getTag(
                                    v_g_4867_,
                                    v___y_4869_,
                                    v___y_4870_,
                                    v___y_4871_,
                                    v___y_4872_,
                                );
                                if lean_obj_tag(v___x_4959_) == 0 {
                                    v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
                                    lean_inc(v_a_4960_);
                                    lean_dec_ref_known(v___x_4959_, 1);
                                    v___x_4961_ = l_Lean_instInhabitedExpr;
                                    v___x_4962_ = lean_array_get_size(v_fst_4950_);
                                    v___x_4963_ = lean_unsigned_to_nat(1);
                                    v___x_4964_ = lean_nat_sub(v___x_4962_, v___x_4963_);
                                    v___x_4965_ =
                                        lean_array_get(v___x_4961_, v_fst_4950_, v___x_4964_);
                                    lean_dec(v___x_4964_);
                                    lean_dec(v_fst_4950_);
                                    v___x_4966_ = l_Lean_Expr_mvarId_x21(v___x_4965_);
                                    lean_dec(v___x_4965_);
                                    lean_inc(v___x_4966_);
                                    v___x_4967_ = l_Lean_MVarId_setTag___redArg(
                                        v___x_4966_,
                                        v_a_4960_,
                                        v___y_4870_,
                                    );
                                    if lean_obj_tag(v___x_4967_) == 0 {
                                        lean_dec(v_a_4879_);
                                        lean_dec(v_tail_4877_);
                                        lean_dec(v_g_4867_);
                                        v_isSharedCheck_4974_ =
                                            (!lean_is_exclusive(v___x_4967_)) as u8;
                                        if v_isSharedCheck_4974_ == 0 {
                                            v_unused_4975_ = lean_ctor_get(v___x_4967_, 0);
                                            lean_dec(v_unused_4975_);
                                            v___x_4969_ = v___x_4967_;
                                            v_isShared_4970_ = v_isSharedCheck_4974_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_dec(v___x_4967_);
                                            v___x_4969_ = lean_box(0);
                                            v_isShared_4970_ = v_isSharedCheck_4974_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_4966_);
                                        v_a_4976_ = lean_ctor_get(v___x_4967_, 0);
                                        v_isSharedCheck_4983_ =
                                            (!lean_is_exclusive(v___x_4967_)) as u8;
                                        if v_isSharedCheck_4983_ == 0 {
                                            v___x_4978_ = v___x_4967_;
                                            v_isShared_4979_ = v_isSharedCheck_4983_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4976_);
                                            lean_dec(v___x_4967_);
                                            v___x_4978_ = lean_box(0);
                                            v_isShared_4979_ = v_isSharedCheck_4983_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_4950_);
                                    v_a_4984_ = lean_ctor_get(v___x_4959_, 0);
                                    v_isSharedCheck_4991_ = (!lean_is_exclusive(v___x_4959_)) as u8;
                                    if v_isSharedCheck_4991_ == 0 {
                                        v___x_4986_ = v___x_4959_;
                                        v_isShared_4987_ = v_isSharedCheck_4991_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4984_);
                                        lean_dec(v___x_4959_);
                                        v___x_4986_ = lean_box(0);
                                        v_isShared_4987_ = v_isSharedCheck_4991_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_fst_4950_);
                                lean_dec(v_a_4899_);
                                v___x_4992_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1_once), _init_l_List_firstM___at___00Lean_Expr_applySymm_spec__1___closed__1);
                                v___x_4993_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_4992_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
                                v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
                                lean_inc(v_a_4994_);
                                v___y_4894_ = v___x_4993_;
                                v_a_4895_ = v_a_4994_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_4950_);
                            lean_dec(v_a_4899_);
                            v_a_4995_ = lean_ctor_get(v___x_4954_, 0);
                            v_isSharedCheck_5002_ = (!lean_is_exclusive(v___x_4954_)) as u8;
                            if v_isSharedCheck_5002_ == 0 {
                                v___x_4997_ = v___x_4954_;
                                v_isShared_4998_ = v_isSharedCheck_5002_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_4995_);
                                lean_dec(v___x_4954_);
                                v___x_4997_ = lean_box(0);
                                v_isShared_4998_ = v_isSharedCheck_5002_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_4951_);
                        lean_dec(v_fst_4950_);
                        lean_dec(v_a_4899_);
                        v_a_5003_ = lean_ctor_get(v___x_4952_, 0);
                        v_isSharedCheck_5010_ = (!lean_is_exclusive(v___x_4952_)) as u8;
                        if v_isSharedCheck_5010_ == 0 {
                            v___x_5005_ = v___x_4952_;
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5003_);
                            lean_dec(v___x_4952_);
                            v___x_5005_ = lean_box(0);
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4899_);
                    v_a_5011_ = lean_ctor_get(v___x_4947_, 0);
                    v_isSharedCheck_5018_ = (!lean_is_exclusive(v___x_4947_)) as u8;
                    if v_isSharedCheck_5018_ == 0 {
                        v___x_5013_ = v___x_4947_;
                        v_isShared_5014_ = v_isSharedCheck_5018_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5011_);
                        lean_dec(v___x_4947_);
                        v___x_5013_ = lean_box(0);
                        v_isShared_5014_ = v_isSharedCheck_5018_;
                        state = 17;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4970_ == 0 {
                    lean_ctor_set(v___x_4969_, 0, v___x_4966_);
                    v___x_4972_ = v___x_4969_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4966_);
                    v___x_4972_ = v_reuseFailAlloc_4973_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4972_;
            }
            9 => {
                lean_inc(v_a_4976_);
                if v_isShared_4979_ == 0 {
                    v___x_4981_ = v___x_4978_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
                    v___x_4981_ = v_reuseFailAlloc_4982_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_4894_ = v___x_4981_;
                v_a_4895_ = v_a_4976_;
                state = 4;
                continue;
            }
            11 => {
                lean_inc(v_a_4984_);
                if v_isShared_4987_ == 0 {
                    v___x_4989_ = v___x_4986_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
                    v___x_4989_ = v_reuseFailAlloc_4990_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_4894_ = v___x_4989_;
                v_a_4895_ = v_a_4984_;
                state = 4;
                continue;
            }
            13 => {
                lean_inc(v_a_4995_);
                if v_isShared_4998_ == 0 {
                    v___x_5000_ = v___x_4997_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_4894_ = v___x_5000_;
                v_a_4895_ = v_a_4995_;
                state = 4;
                continue;
            }
            15 => {
                lean_inc(v_a_5003_);
                if v_isShared_5006_ == 0 {
                    v___x_5008_ = v___x_5005_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_4894_ = v___x_5008_;
                v_a_4895_ = v_a_5003_;
                state = 4;
                continue;
            }
            17 => {
                lean_inc(v_a_5011_);
                if v_isShared_5014_ == 0 {
                    v___x_5016_ = v___x_5013_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_a_5011_);
                    v___x_5016_ = v_reuseFailAlloc_5017_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_4894_ = v___x_5016_;
                v_a_4895_ = v_a_5011_;
                state = 4;
                continue;
            }
            19 => {
                lean_inc(v_a_5021_);
                if v_isShared_5024_ == 0 {
                    v___x_5026_ = v___x_5023_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
                    v___x_5026_ = v_reuseFailAlloc_5027_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___y_4894_ = v___x_5026_;
                v_a_4895_ = v_a_5021_;
                state = 4;
                continue;
            }
            21 => {
                lean_inc(v_a_5029_);
                if v_isShared_5032_ == 0 {
                    v___x_5034_ = v___x_5031_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_4894_ = v___x_5034_;
                v_a_4895_ = v_a_5029_;
                state = 4;
                continue;
            }
            23 => {
                if v_isShared_5040_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_firstM___at___00Lean_MVarId_applySymm_spec__1___boxed(
    mut v_g_5045_: *mut LeanObject,
    mut v_x_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5052_: *mut LeanObject = core::ptr::null_mut();
    v_res_5052_ = l_List_firstM___at___00Lean_MVarId_applySymm_spec__1(
        v_g_5045_,
        v_x_5046_,
        v___y_5047_,
        v___y_5048_,
        v___y_5049_,
        v___y_5050_,
    );
    lean_dec(v___y_5050_);
    lean_dec_ref(v___y_5049_);
    lean_dec(v___y_5048_);
    lean_dec_ref(v___y_5047_);
    return v_res_5052_;
}
pub unsafe fn l_Lean_MVarId_applySymm(
    mut v_g_5053_: *mut LeanObject,
    mut v_a_5054_: *mut LeanObject,
    mut v_a_5055_: *mut LeanObject,
    mut v_a_5056_: *mut LeanObject,
    mut v_a_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5072_: u8 = 0;
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut v___x_5088_: u8 = 0;
    let mut v___x_5089_: u8 = 0;
    let mut v_a_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5097_: u8 = 0;
    let mut v_a_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5101_: u8 = 0;
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut v_a_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_g_5053_);
                v___x_5059_ =
                    l_Lean_MVarId_getType(v_g_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_);
                if lean_obj_tag(v___x_5059_) == 0 {
                    v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
                    lean_inc(v_a_5060_);
                    lean_dec_ref_known(v___x_5059_, 1);
                    v___x_5061_ =
                        l_Lean_instantiateMVars___at___00Lean_Expr_applySymm_spec__0___redArg(
                            v_a_5060_, v_a_5055_,
                        );
                    v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
                    lean_inc(v_a_5062_);
                    lean_dec_ref(v___x_5061_);
                    v___x_5063_ = l_Lean_Expr_cleanupAnnotations(v_a_5062_);
                    lean_inc_ref(v___x_5063_);
                    v___x_5064_ = l_Lean_Expr_getSymmLems(
                        v___x_5063_,
                        v_a_5054_,
                        v_a_5055_,
                        v_a_5056_,
                        v_a_5057_,
                    );
                    if lean_obj_tag(v___x_5064_) == 0 {
                        v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
                        lean_inc(v_a_5065_);
                        lean_dec_ref_known(v___x_5064_, 1);
                        v___x_5066_ = l_Lean_Meta_saveState___redArg(v_a_5055_, v_a_5057_);
                        if lean_obj_tag(v___x_5066_) == 0 {
                            v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
                            lean_inc(v_a_5067_);
                            lean_dec_ref_known(v___x_5066_, 1);
                            v___x_5068_ = lean_array_to_list(v_a_5065_);
                            v___x_5069_ = l_List_firstM___at___00Lean_MVarId_applySymm_spec__1(
                                v_g_5053_,
                                v___x_5068_,
                                v_a_5054_,
                                v_a_5055_,
                                v_a_5056_,
                                v_a_5057_,
                            );
                            if lean_obj_tag(v___x_5069_) == 0 {
                                lean_dec(v_a_5067_);
                                lean_dec_ref(v___x_5063_);
                                return v___x_5069_;
                            } else {
                                v_a_5070_ = lean_ctor_get(v___x_5069_, 0);
                                lean_inc(v_a_5070_);
                                v___x_5088_ = l_Lean_Exception_isInterrupt(v_a_5070_);
                                if v___x_5088_ == 0 {
                                    v___x_5089_ = l_Lean_Exception_isRuntime(v_a_5070_);
                                    v___y_5072_ = v___x_5089_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_5070_);
                                    v___y_5072_ = v___x_5088_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5065_);
                            lean_dec_ref(v___x_5063_);
                            lean_dec(v_g_5053_);
                            v_a_5090_ = lean_ctor_get(v___x_5066_, 0);
                            v_isSharedCheck_5097_ = (!lean_is_exclusive(v___x_5066_)) as u8;
                            if v_isSharedCheck_5097_ == 0 {
                                v___x_5092_ = v___x_5066_;
                                v_isShared_5093_ = v_isSharedCheck_5097_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5090_);
                                lean_dec(v___x_5066_);
                                v___x_5092_ = lean_box(0);
                                v_isShared_5093_ = v_isSharedCheck_5097_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_5063_);
                        lean_dec(v_g_5053_);
                        v_a_5098_ = lean_ctor_get(v___x_5064_, 0);
                        v_isSharedCheck_5105_ = (!lean_is_exclusive(v___x_5064_)) as u8;
                        if v_isSharedCheck_5105_ == 0 {
                            v___x_5100_ = v___x_5064_;
                            v_isShared_5101_ = v_isSharedCheck_5105_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5098_);
                            lean_dec(v___x_5064_);
                            v___x_5100_ = lean_box(0);
                            v_isShared_5101_ = v_isSharedCheck_5105_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_g_5053_);
                    v_a_5106_ = lean_ctor_get(v___x_5059_, 0);
                    v_isSharedCheck_5113_ = (!lean_is_exclusive(v___x_5059_)) as u8;
                    if v_isSharedCheck_5113_ == 0 {
                        v___x_5108_ = v___x_5059_;
                        v_isShared_5109_ = v_isSharedCheck_5113_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5106_);
                        lean_dec(v___x_5059_);
                        v___x_5108_ = lean_box(0);
                        v_isShared_5109_ = v_isSharedCheck_5113_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5072_ == 0 {
                    lean_dec_ref_known(v___x_5069_, 1);
                    v___x_5073_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_5067_, v_a_5055_, v_a_5057_);
                    lean_dec(v_a_5067_);
                    if lean_obj_tag(v___x_5073_) == 0 {
                        lean_dec_ref_known(v___x_5073_, 1);
                        v___x_5074_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__1_once),
                            _init_l_Lean_Expr_applySymm___closed__1,
                        );
                        v___x_5075_ = l_Lean_indentExpr(v___x_5063_);
                        v___x_5076_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5076_, 0, v___x_5074_);
                        lean_ctor_set(v___x_5076_, 1, v___x_5075_);
                        v___x_5077_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Expr_applySymm___closed__4_once),
                            _init_l_Lean_Expr_applySymm___closed__4,
                        );
                        v___x_5078_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5078_, 0, v___x_5076_);
                        lean_ctor_set(v___x_5078_, 1, v___x_5077_);
                        v___x_5079_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2__spec__1___redArg(v___x_5078_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_);
                        return v___x_5079_;
                    } else {
                        lean_dec_ref(v___x_5063_);
                        v_a_5080_ = lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5087_ = (!lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5087_ == 0 {
                            v___x_5082_ = v___x_5073_;
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5080_);
                            lean_dec(v___x_5073_);
                            v___x_5082_ = lean_box(0);
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5067_);
                    lean_dec_ref(v___x_5063_);
                    return v___x_5069_;
                }
            }
            2 => {
                if v_isShared_5083_ == 0 {
                    v___x_5085_ = v___x_5082_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5085_;
            }
            4 => {
                if v_isShared_5093_ == 0 {
                    v___x_5095_ = v___x_5092_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
                    v___x_5095_ = v_reuseFailAlloc_5096_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5095_;
            }
            6 => {
                if v_isShared_5101_ == 0 {
                    v___x_5103_ = v___x_5100_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
                    v___x_5103_ = v_reuseFailAlloc_5104_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5103_;
            }
            8 => {
                if v_isShared_5109_ == 0 {
                    v___x_5111_ = v___x_5108_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
                    v___x_5111_ = v_reuseFailAlloc_5112_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applySymm___boxed(
    mut v_g_5114_: *mut LeanObject,
    mut v_a_5115_: *mut LeanObject,
    mut v_a_5116_: *mut LeanObject,
    mut v_a_5117_: *mut LeanObject,
    mut v_a_5118_: *mut LeanObject,
    mut v_a_5119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5120_: *mut LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_Lean_MVarId_applySymm(v_g_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
    lean_dec(v_a_5118_);
    lean_dec_ref(v_a_5117_);
    lean_dec(v_a_5116_);
    lean_dec_ref(v_a_5115_);
    return v_res_5120_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0(
    mut v_mvarId_5121_: *mut LeanObject,
    mut v_val_5122_: *mut LeanObject,
    mut v___y_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    v___x_5128_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0___redArg(
        v_mvarId_5121_,
        v_val_5122_,
        v___y_5124_,
    );
    return v___x_5128_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0___boxed(
    mut v_mvarId_5129_: *mut LeanObject,
    mut v_val_5130_: *mut LeanObject,
    mut v___y_5131_: *mut LeanObject,
    mut v___y_5132_: *mut LeanObject,
    mut v___y_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5136_: *mut LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0(
        v_mvarId_5129_,
        v_val_5130_,
        v___y_5131_,
        v___y_5132_,
        v___y_5133_,
        v___y_5134_,
    );
    lean_dec(v___y_5134_);
    lean_dec_ref(v___y_5133_);
    lean_dec(v___y_5132_);
    lean_dec_ref(v___y_5131_);
    return v_res_5136_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0(
    mut v_00_u03b2_5137_: *mut LeanObject,
    mut v_x_5138_: *mut LeanObject,
    mut v_x_5139_: *mut LeanObject,
    mut v_x_5140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    v___x_5141_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0___redArg(v_x_5138_, v_x_5139_, v_x_5140_);
    return v___x_5141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5142_: *mut LeanObject,
    mut v_x_5143_: *mut LeanObject,
    mut v_x_5144_: usize,
    mut v_x_5145_: usize,
    mut v_x_5146_: *mut LeanObject,
    mut v_x_5147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    v___x_5148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___redArg(v_x_5143_, v_x_5144_, v_x_5145_, v_x_5146_, v_x_5147_);
    return v___x_5148_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5149_: *mut LeanObject,
    mut v_x_5150_: *mut LeanObject,
    mut v_x_5151_: *mut LeanObject,
    mut v_x_5152_: *mut LeanObject,
    mut v_x_5153_: *mut LeanObject,
    mut v_x_5154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4542__boxed_5155_: usize = 0;
    let mut v_x_4543__boxed_5156_: usize = 0;
    let mut v_res_5157_: *mut LeanObject = core::ptr::null_mut();
    v_x_4542__boxed_5155_ = lean_unbox_usize(v_x_5151_);
    lean_dec(v_x_5151_);
    v_x_4543__boxed_5156_ = lean_unbox_usize(v_x_5152_);
    lean_dec(v_x_5152_);
    v_res_5157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1(v_00_u03b2_5149_, v_x_5150_, v_x_4542__boxed_5155_, v_x_4543__boxed_5156_, v_x_5153_, v_x_5154_);
    return v_res_5157_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5158_: *mut LeanObject,
    mut v_n_5159_: *mut LeanObject,
    mut v_k_5160_: *mut LeanObject,
    mut v_v_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    v___x_5162_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3___redArg(v_n_5159_, v_k_5160_, v_v_5161_);
    return v___x_5162_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_5163_: *mut LeanObject,
    mut v_depth_5164_: usize,
    mut v_keys_5165_: *mut LeanObject,
    mut v_vals_5166_: *mut LeanObject,
    mut v_heq_5167_: *mut LeanObject,
    mut v_i_5168_: *mut LeanObject,
    mut v_entries_5169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    v___x_5170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_5164_, v_keys_5165_, v_vals_5166_, v_i_5168_, v_entries_5169_);
    return v___x_5170_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_5171_: *mut LeanObject,
    mut v_depth_5172_: *mut LeanObject,
    mut v_keys_5173_: *mut LeanObject,
    mut v_vals_5174_: *mut LeanObject,
    mut v_heq_5175_: *mut LeanObject,
    mut v_i_5176_: *mut LeanObject,
    mut v_entries_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5178_: usize = 0;
    let mut v_res_5179_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5178_ = lean_unbox_usize(v_depth_5172_);
    lean_dec(v_depth_5172_);
    v_res_5179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_5171_, v_depth_boxed_5178_, v_keys_5173_, v_vals_5174_, v_heq_5175_, v_i_5176_, v_entries_5177_);
    lean_dec_ref(v_vals_5174_);
    lean_dec_ref(v_keys_5173_);
    return v_res_5179_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3_spec__4(
    mut v_00_u03b2_5180_: *mut LeanObject,
    mut v_x_5181_: *mut LeanObject,
    mut v_x_5182_: *mut LeanObject,
    mut v_x_5183_: *mut LeanObject,
    mut v_x_5184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    v___x_5185_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applySymm_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_5181_, v_x_5182_, v_x_5183_, v_x_5184_);
    return v___x_5185_;
}
pub unsafe fn l_Lean_MVarId_applySymmAt(
    mut v_h_5186_: *mut LeanObject,
    mut v_g_5187_: *mut LeanObject,
    mut v_a_5188_: *mut LeanObject,
    mut v_a_5189_: *mut LeanObject,
    mut v_a_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v_mvarId_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5206_: u8 = 0;
    let mut v_a_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_a_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5218_: u8 = 0;
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_h_5186_);
                v___x_5193_ = l_Lean_Expr_fvar___override(v_h_5186_);
                v___x_5194_ =
                    l_Lean_Expr_applySymm(v___x_5193_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_);
                if lean_obj_tag(v___x_5194_) == 0 {
                    v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
                    lean_inc(v_a_5195_);
                    lean_dec_ref_known(v___x_5194_, 1);
                    v___x_5196_ = lean_box(0);
                    v___x_5197_ = l_Lean_MVarId_replace(
                        v_g_5187_,
                        v_h_5186_,
                        v_a_5195_,
                        v___x_5196_,
                        v___x_5196_,
                        v_a_5188_,
                        v_a_5189_,
                        v_a_5190_,
                        v_a_5191_,
                    );
                    if lean_obj_tag(v___x_5197_) == 0 {
                        v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5206_ = (!lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5206_ == 0 {
                            v___x_5200_ = v___x_5197_;
                            v_isShared_5201_ = v_isSharedCheck_5206_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5198_);
                            lean_dec(v___x_5197_);
                            v___x_5200_ = lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5206_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5207_ = lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5214_ = (!lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5214_ == 0 {
                            v___x_5209_ = v___x_5197_;
                            v_isShared_5210_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5207_);
                            lean_dec(v___x_5197_);
                            v___x_5209_ = lean_box(0);
                            v_isShared_5210_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_g_5187_);
                    lean_dec(v_h_5186_);
                    v_a_5215_ = lean_ctor_get(v___x_5194_, 0);
                    v_isSharedCheck_5222_ = (!lean_is_exclusive(v___x_5194_)) as u8;
                    if v_isSharedCheck_5222_ == 0 {
                        v___x_5217_ = v___x_5194_;
                        v_isShared_5218_ = v_isSharedCheck_5222_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5215_);
                        lean_dec(v___x_5194_);
                        v___x_5217_ = lean_box(0);
                        v_isShared_5218_ = v_isSharedCheck_5222_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_5202_ = lean_ctor_get(v_a_5198_, 1);
                lean_inc(v_mvarId_5202_);
                lean_dec(v_a_5198_);
                if v_isShared_5201_ == 0 {
                    lean_ctor_set(v___x_5200_, 0, v_mvarId_5202_);
                    v___x_5204_ = v___x_5200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5205_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_mvarId_5202_);
                    v___x_5204_ = v_reuseFailAlloc_5205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5204_;
            }
            3 => {
                if v_isShared_5210_ == 0 {
                    v___x_5212_ = v___x_5209_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
                    v___x_5212_ = v_reuseFailAlloc_5213_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5212_;
            }
            5 => {
                if v_isShared_5218_ == 0 {
                    v___x_5220_ = v___x_5217_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
                    v___x_5220_ = v_reuseFailAlloc_5221_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applySymmAt___boxed(
    mut v_h_5223_: *mut LeanObject,
    mut v_g_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
    mut v_a_5227_: *mut LeanObject,
    mut v_a_5228_: *mut LeanObject,
    mut v_a_5229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5230_: *mut LeanObject = core::ptr::null_mut();
    v_res_5230_ = l_Lean_MVarId_applySymmAt(
        v_h_5223_, v_g_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_,
    );
    lean_dec(v_a_5228_);
    lean_dec_ref(v_a_5227_);
    lean_dec(v_a_5226_);
    lean_dec_ref(v_a_5225_);
    return v_res_5230_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4___redArg(
    mut v_mvarId_5231_: *mut LeanObject,
    mut v_x_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut v_a_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5250_: u8 = 0;
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5231_,
                    v_x_5232_,
                    v___y_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                );
                if lean_obj_tag(v___x_5238_) == 0 {
                    v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5246_ = (!lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5246_ == 0 {
                        v___x_5241_ = v___x_5238_;
                        v_isShared_5242_ = v_isSharedCheck_5246_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5239_);
                        lean_dec(v___x_5238_);
                        v___x_5241_ = lean_box(0);
                        v_isShared_5242_ = v_isSharedCheck_5246_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5247_ = lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5254_ = (!lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5254_ == 0 {
                        v___x_5249_ = v___x_5238_;
                        v_isShared_5250_ = v_isSharedCheck_5254_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5247_);
                        lean_dec(v___x_5238_);
                        v___x_5249_ = lean_box(0);
                        v_isShared_5250_ = v_isSharedCheck_5254_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5242_ == 0 {
                    v___x_5244_ = v___x_5241_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
                    v___x_5244_ = v_reuseFailAlloc_5245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5244_;
            }
            3 => {
                if v_isShared_5250_ == 0 {
                    v___x_5252_ = v___x_5249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
                    v___x_5252_ = v_reuseFailAlloc_5253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4___redArg___boxed(
    mut v_mvarId_5255_: *mut LeanObject,
    mut v_x_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
    mut v___y_5258_: *mut LeanObject,
    mut v___y_5259_: *mut LeanObject,
    mut v___y_5260_: *mut LeanObject,
    mut v___y_5261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5262_: *mut LeanObject = core::ptr::null_mut();
    v_res_5262_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4___redArg(
        v_mvarId_5255_,
        v_x_5256_,
        v___y_5257_,
        v___y_5258_,
        v___y_5259_,
        v___y_5260_,
    );
    lean_dec(v___y_5260_);
    lean_dec_ref(v___y_5259_);
    lean_dec(v___y_5258_);
    lean_dec_ref(v___y_5257_);
    return v_res_5262_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4(
    mut v_00_u03b1_5263_: *mut LeanObject,
    mut v_mvarId_5264_: *mut LeanObject,
    mut v_x_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    v___x_5271_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4___redArg(
        v_mvarId_5264_,
        v_x_5265_,
        v___y_5266_,
        v___y_5267_,
        v___y_5268_,
        v___y_5269_,
    );
    return v___x_5271_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4___boxed(
    mut v_00_u03b1_5272_: *mut LeanObject,
    mut v_mvarId_5273_: *mut LeanObject,
    mut v_x_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5280_: *mut LeanObject = core::ptr::null_mut();
    v_res_5280_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4(
        v_00_u03b1_5272_,
        v_mvarId_5273_,
        v_x_5274_,
        v___y_5275_,
        v___y_5276_,
        v___y_5277_,
        v___y_5278_,
    );
    lean_dec(v___y_5278_);
    lean_dec_ref(v___y_5277_);
    lean_dec(v___y_5276_);
    lean_dec_ref(v___y_5275_);
    return v_res_5280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_symmSaturate_spec__1(
    mut v_sz_5281_: usize,
    mut v_i_5282_: usize,
    mut v_bs_5283_: *mut LeanObject,
    mut v___y_5284_: *mut LeanObject,
    mut v___y_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
    mut v___y_5287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5289_: u8 = 0;
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: usize = 0;
    let mut v___x_5297_: usize = 0;
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5303_: u8 = 0;
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5289_ = lean_usize_dec_lt(v_i_5282_, v_sz_5281_);
                if v___x_5289_ == 0 {
                    v___x_5290_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5290_, 0, v_bs_5283_);
                    return v___x_5290_;
                } else {
                    v_v_5291_ = lean_array_uget_borrowed(v_bs_5283_, v_i_5282_);
                    lean_inc(v___y_5287_);
                    lean_inc_ref(v___y_5286_);
                    lean_inc(v___y_5285_);
                    lean_inc_ref(v___y_5284_);
                    lean_inc(v_v_5291_);
                    v___x_5292_ = lean_infer_type(
                        v_v_5291_,
                        v___y_5284_,
                        v___y_5285_,
                        v___y_5286_,
                        v___y_5287_,
                    );
                    if lean_obj_tag(v___x_5292_) == 0 {
                        v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
                        lean_inc(v_a_5293_);
                        lean_dec_ref_known(v___x_5292_, 1);
                        v___x_5294_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5295_ = lean_array_uset(v_bs_5283_, v_i_5282_, v___x_5294_);
                        v___x_5296_ = 1usize;
                        v___x_5297_ = lean_usize_add(v_i_5282_, v___x_5296_);
                        v___x_5298_ = lean_array_uset(v_bs_x27_5295_, v_i_5282_, v_a_5293_);
                        v_i_5282_ = v___x_5297_;
                        v_bs_5283_ = v___x_5298_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5283_);
                        v_a_5300_ = lean_ctor_get(v___x_5292_, 0);
                        v_isSharedCheck_5307_ = (!lean_is_exclusive(v___x_5292_)) as u8;
                        if v_isSharedCheck_5307_ == 0 {
                            v___x_5302_ = v___x_5292_;
                            v_isShared_5303_ = v_isSharedCheck_5307_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5300_);
                            lean_dec(v___x_5292_);
                            v___x_5302_ = lean_box(0);
                            v_isShared_5303_ = v_isSharedCheck_5307_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5303_ == 0 {
                    v___x_5305_ = v___x_5302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
                    v___x_5305_ = v_reuseFailAlloc_5306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_symmSaturate_spec__1___boxed(
    mut v_sz_5308_: *mut LeanObject,
    mut v_i_5309_: *mut LeanObject,
    mut v_bs_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5316_: usize = 0;
    let mut v_i_boxed_5317_: usize = 0;
    let mut v_res_5318_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5316_ = lean_unbox_usize(v_sz_5308_);
    lean_dec(v_sz_5308_);
    v_i_boxed_5317_ = lean_unbox_usize(v_i_5309_);
    lean_dec(v_i_5309_);
    v_res_5318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_symmSaturate_spec__1(v_sz_boxed_5316_, v_i_boxed_5317_, v_bs_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
    lean_dec(v___y_5314_);
    lean_dec_ref(v___y_5313_);
    lean_dec(v___y_5312_);
    lean_dec_ref(v___y_5311_);
    return v_res_5318_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8___redArg(
    mut v_as_5319_: *mut LeanObject,
    mut v_sz_5320_: usize,
    mut v_i_5321_: usize,
    mut v_b_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5324_: u8 = 0;
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: usize = 0;
    let mut v___x_5336_: usize = 0;
    let mut v_reuseFailAlloc_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5344_: u8 = 0;
    let mut v_unused_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5324_ = lean_usize_dec_lt(v_i_5321_, v_sz_5320_);
                if v___x_5324_ == 0 {
                    v___x_5325_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5325_, 0, v_b_5322_);
                    return v___x_5325_;
                } else {
                    v_snd_5326_ = lean_ctor_get(v_b_5322_, 1);
                    v_isSharedCheck_5344_ = (!lean_is_exclusive(v_b_5322_)) as u8;
                    if v_isSharedCheck_5344_ == 0 {
                        v_unused_5345_ = lean_ctor_get(v_b_5322_, 0);
                        lean_dec(v_unused_5345_);
                        v___x_5328_ = v_b_5322_;
                        v_isShared_5329_ = v_isSharedCheck_5344_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5326_);
                        lean_dec(v_b_5322_);
                        v___x_5328_ = lean_box(0);
                        v_isShared_5329_ = v_isSharedCheck_5344_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5330_ = lean_box(0);
                v_a_5339_ = lean_array_uget_borrowed(v_as_5319_, v_i_5321_);
                if lean_obj_tag(v_a_5339_) == 0 {
                    v_a_5332_ = v_snd_5326_;
                    state = 2;
                    continue;
                } else {
                    v_val_5340_ = lean_ctor_get(v_a_5339_, 0);
                    v___x_5341_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5340_);
                    if v___x_5341_ == 0 {
                        lean_inc(v_val_5340_);
                        v___x_5342_ = l_Lean_LocalDecl_toExpr(v_val_5340_);
                        v___x_5343_ = lean_array_push(v_snd_5326_, v___x_5342_);
                        v_a_5332_ = v___x_5343_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5332_ = v_snd_5326_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5329_ == 0 {
                    lean_ctor_set(v___x_5328_, 1, v_a_5332_);
                    lean_ctor_set(v___x_5328_, 0, v___x_5330_);
                    v___x_5334_ = v___x_5328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5330_);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 1, v_a_5332_);
                    v___x_5334_ = v_reuseFailAlloc_5338_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5335_ = 1usize;
                v___x_5336_ = lean_usize_add(v_i_5321_, v___x_5335_);
                v_i_5321_ = v___x_5336_;
                v_b_5322_ = v___x_5334_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8___redArg___boxed(
    mut v_as_5346_: *mut LeanObject,
    mut v_sz_5347_: *mut LeanObject,
    mut v_i_5348_: *mut LeanObject,
    mut v_b_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5351_: usize = 0;
    let mut v_i_boxed_5352_: usize = 0;
    let mut v_res_5353_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5351_ = lean_unbox_usize(v_sz_5347_);
    lean_dec(v_sz_5347_);
    v_i_boxed_5352_ = lean_unbox_usize(v_i_5348_);
    lean_dec(v_i_5348_);
    v_res_5353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8___redArg(v_as_5346_, v_sz_boxed_5351_, v_i_boxed_5352_, v_b_5349_);
    lean_dec_ref(v_as_5346_);
    return v_res_5353_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7(
    mut v_as_5354_: *mut LeanObject,
    mut v_sz_5355_: usize,
    mut v_i_5356_: usize,
    mut v_b_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5363_: u8 = 0;
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: usize = 0;
    let mut v___x_5375_: usize = 0;
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5383_: u8 = 0;
    let mut v_unused_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5363_ = lean_usize_dec_lt(v_i_5356_, v_sz_5355_);
                if v___x_5363_ == 0 {
                    v___x_5364_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5364_, 0, v_b_5357_);
                    return v___x_5364_;
                } else {
                    v_snd_5365_ = lean_ctor_get(v_b_5357_, 1);
                    v_isSharedCheck_5383_ = (!lean_is_exclusive(v_b_5357_)) as u8;
                    if v_isSharedCheck_5383_ == 0 {
                        v_unused_5384_ = lean_ctor_get(v_b_5357_, 0);
                        lean_dec(v_unused_5384_);
                        v___x_5367_ = v_b_5357_;
                        v_isShared_5368_ = v_isSharedCheck_5383_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5365_);
                        lean_dec(v_b_5357_);
                        v___x_5367_ = lean_box(0);
                        v_isShared_5368_ = v_isSharedCheck_5383_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5369_ = lean_box(0);
                v_a_5378_ = lean_array_uget_borrowed(v_as_5354_, v_i_5356_);
                if lean_obj_tag(v_a_5378_) == 0 {
                    v_a_5371_ = v_snd_5365_;
                    state = 2;
                    continue;
                } else {
                    v_val_5379_ = lean_ctor_get(v_a_5378_, 0);
                    v___x_5380_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5379_);
                    if v___x_5380_ == 0 {
                        lean_inc(v_val_5379_);
                        v___x_5381_ = l_Lean_LocalDecl_toExpr(v_val_5379_);
                        v___x_5382_ = lean_array_push(v_snd_5365_, v___x_5381_);
                        v_a_5371_ = v___x_5382_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5371_ = v_snd_5365_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5368_ == 0 {
                    lean_ctor_set(v___x_5367_, 1, v_a_5371_);
                    lean_ctor_set(v___x_5367_, 0, v___x_5369_);
                    v___x_5373_ = v___x_5367_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5377_, 0, v___x_5369_);
                    lean_ctor_set(v_reuseFailAlloc_5377_, 1, v_a_5371_);
                    v___x_5373_ = v_reuseFailAlloc_5377_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5374_ = 1usize;
                v___x_5375_ = lean_usize_add(v_i_5356_, v___x_5374_);
                v___x_5376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8___redArg(v_as_5354_, v_sz_5355_, v___x_5375_, v___x_5373_);
                return v___x_5376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_as_5385_: *mut LeanObject,
    mut v_sz_5386_: *mut LeanObject,
    mut v_i_5387_: *mut LeanObject,
    mut v_b_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
    mut v___y_5392_: *mut LeanObject,
    mut v___y_5393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5394_: usize = 0;
    let mut v_i_boxed_5395_: usize = 0;
    let mut v_res_5396_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5394_ = lean_unbox_usize(v_sz_5386_);
    lean_dec(v_sz_5386_);
    v_i_boxed_5395_ = lean_unbox_usize(v_i_5387_);
    lean_dec(v_i_5387_);
    v_res_5396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7(v_as_5385_, v_sz_boxed_5394_, v_i_boxed_5395_, v_b_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
    lean_dec(v___y_5392_);
    lean_dec_ref(v___y_5391_);
    lean_dec(v___y_5390_);
    lean_dec_ref(v___y_5389_);
    lean_dec_ref(v_as_5385_);
    return v_res_5396_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2(
    mut v_init_5397_: *mut LeanObject,
    mut v_n_5398_: *mut LeanObject,
    mut v_b_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
    mut v___y_5402_: *mut LeanObject,
    mut v___y_5403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5408_: usize = 0;
    let mut v___x_5409_: usize = 0;
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5414_: u8 = 0;
    let mut v_fst_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5425_: u8 = 0;
    let mut v_a_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5429_: u8 = 0;
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5433_: u8 = 0;
    let mut v_vs_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5437_: usize = 0;
    let mut v___x_5438_: usize = 0;
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v_fst_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut v_a_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5458_: u8 = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5398_) == 0 {
                    v_cs_5405_ = lean_ctor_get(v_n_5398_, 0);
                    v___x_5406_ = lean_box(0);
                    v___x_5407_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5407_, 0, v___x_5406_);
                    lean_ctor_set(v___x_5407_, 1, v_b_5399_);
                    v_sz_5408_ = lean_array_size(v_cs_5405_);
                    v___x_5409_ = 0usize;
                    v___x_5410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__6(v_init_5397_, v_cs_5405_, v_sz_5408_, v___x_5409_, v___x_5407_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
                    if lean_obj_tag(v___x_5410_) == 0 {
                        v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
                        v_isSharedCheck_5425_ = (!lean_is_exclusive(v___x_5410_)) as u8;
                        if v_isSharedCheck_5425_ == 0 {
                            v___x_5413_ = v___x_5410_;
                            v_isShared_5414_ = v_isSharedCheck_5425_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5411_);
                            lean_dec(v___x_5410_);
                            v___x_5413_ = lean_box(0);
                            v_isShared_5414_ = v_isSharedCheck_5425_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5426_ = lean_ctor_get(v___x_5410_, 0);
                        v_isSharedCheck_5433_ = (!lean_is_exclusive(v___x_5410_)) as u8;
                        if v_isSharedCheck_5433_ == 0 {
                            v___x_5428_ = v___x_5410_;
                            v_isShared_5429_ = v_isSharedCheck_5433_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5426_);
                            lean_dec(v___x_5410_);
                            v___x_5428_ = lean_box(0);
                            v_isShared_5429_ = v_isSharedCheck_5433_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5434_ = lean_ctor_get(v_n_5398_, 0);
                    v___x_5435_ = lean_box(0);
                    v___x_5436_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5436_, 0, v___x_5435_);
                    lean_ctor_set(v___x_5436_, 1, v_b_5399_);
                    v_sz_5437_ = lean_array_size(v_vs_5434_);
                    v___x_5438_ = 0usize;
                    v___x_5439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7(v_vs_5434_, v_sz_5437_, v___x_5438_, v___x_5436_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
                    if lean_obj_tag(v___x_5439_) == 0 {
                        v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
                        v_isSharedCheck_5454_ = (!lean_is_exclusive(v___x_5439_)) as u8;
                        if v_isSharedCheck_5454_ == 0 {
                            v___x_5442_ = v___x_5439_;
                            v_isShared_5443_ = v_isSharedCheck_5454_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5440_);
                            lean_dec(v___x_5439_);
                            v___x_5442_ = lean_box(0);
                            v_isShared_5443_ = v_isSharedCheck_5454_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5455_ = lean_ctor_get(v___x_5439_, 0);
                        v_isSharedCheck_5462_ = (!lean_is_exclusive(v___x_5439_)) as u8;
                        if v_isSharedCheck_5462_ == 0 {
                            v___x_5457_ = v___x_5439_;
                            v_isShared_5458_ = v_isSharedCheck_5462_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5455_);
                            lean_dec(v___x_5439_);
                            v___x_5457_ = lean_box(0);
                            v_isShared_5458_ = v_isSharedCheck_5462_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5415_ = lean_ctor_get(v_a_5411_, 0);
                if lean_obj_tag(v_fst_5415_) == 0 {
                    v_snd_5416_ = lean_ctor_get(v_a_5411_, 1);
                    lean_inc(v_snd_5416_);
                    lean_dec(v_a_5411_);
                    v___x_5417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5417_, 0, v_snd_5416_);
                    if v_isShared_5414_ == 0 {
                        lean_ctor_set(v___x_5413_, 0, v___x_5417_);
                        v___x_5419_ = v___x_5413_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5417_);
                        v___x_5419_ = v_reuseFailAlloc_5420_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5415_);
                    lean_dec(v_a_5411_);
                    v_val_5421_ = lean_ctor_get(v_fst_5415_, 0);
                    lean_inc(v_val_5421_);
                    lean_dec_ref_known(v_fst_5415_, 1);
                    if v_isShared_5414_ == 0 {
                        lean_ctor_set(v___x_5413_, 0, v_val_5421_);
                        v___x_5423_ = v___x_5413_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_val_5421_);
                        v___x_5423_ = v_reuseFailAlloc_5424_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5419_;
            }
            3 => {
                return v___x_5423_;
            }
            4 => {
                if v_isShared_5429_ == 0 {
                    v___x_5431_ = v___x_5428_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
                    v___x_5431_ = v_reuseFailAlloc_5432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5431_;
            }
            6 => {
                v_fst_5444_ = lean_ctor_get(v_a_5440_, 0);
                if lean_obj_tag(v_fst_5444_) == 0 {
                    v_snd_5445_ = lean_ctor_get(v_a_5440_, 1);
                    lean_inc(v_snd_5445_);
                    lean_dec(v_a_5440_);
                    v___x_5446_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5446_, 0, v_snd_5445_);
                    if v_isShared_5443_ == 0 {
                        lean_ctor_set(v___x_5442_, 0, v___x_5446_);
                        v___x_5448_ = v___x_5442_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5446_);
                        v___x_5448_ = v_reuseFailAlloc_5449_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5444_);
                    lean_dec(v_a_5440_);
                    v_val_5450_ = lean_ctor_get(v_fst_5444_, 0);
                    lean_inc(v_val_5450_);
                    lean_dec_ref_known(v_fst_5444_, 1);
                    if v_isShared_5443_ == 0 {
                        lean_ctor_set(v___x_5442_, 0, v_val_5450_);
                        v___x_5452_ = v___x_5442_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_val_5450_);
                        v___x_5452_ = v_reuseFailAlloc_5453_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5448_;
            }
            8 => {
                return v___x_5452_;
            }
            9 => {
                if v_isShared_5458_ == 0 {
                    v___x_5460_ = v___x_5457_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
                    v___x_5460_ = v_reuseFailAlloc_5461_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__6(
    mut v_init_5463_: *mut LeanObject,
    mut v_as_5464_: *mut LeanObject,
    mut v_sz_5465_: usize,
    mut v_i_5466_: usize,
    mut v_b_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
    mut v___y_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5473_: u8 = 0;
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5478_: u8 = 0;
    let mut v_a_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5484_: u8 = 0;
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: usize = 0;
    let mut v___x_5497_: usize = 0;
    let mut v_reuseFailAlloc_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut v_a_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5504_: u8 = 0;
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5508_: u8 = 0;
    let mut v_isSharedCheck_5509_: u8 = 0;
    let mut v_unused_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5473_ = lean_usize_dec_lt(v_i_5466_, v_sz_5465_);
                if v___x_5473_ == 0 {
                    v___x_5474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5474_, 0, v_b_5467_);
                    return v___x_5474_;
                } else {
                    v_snd_5475_ = lean_ctor_get(v_b_5467_, 1);
                    v_isSharedCheck_5509_ = (!lean_is_exclusive(v_b_5467_)) as u8;
                    if v_isSharedCheck_5509_ == 0 {
                        v_unused_5510_ = lean_ctor_get(v_b_5467_, 0);
                        lean_dec(v_unused_5510_);
                        v___x_5477_ = v_b_5467_;
                        v_isShared_5478_ = v_isSharedCheck_5509_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5475_);
                        lean_dec(v_b_5467_);
                        v___x_5477_ = lean_box(0);
                        v_isShared_5478_ = v_isSharedCheck_5509_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5479_ = lean_array_uget_borrowed(v_as_5464_, v_i_5466_);
                lean_inc(v_snd_5475_);
                v___x_5480_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2(v_init_5463_, v_a_5479_, v_snd_5475_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
                if lean_obj_tag(v___x_5480_) == 0 {
                    v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
                    v_isSharedCheck_5500_ = (!lean_is_exclusive(v___x_5480_)) as u8;
                    if v_isSharedCheck_5500_ == 0 {
                        v___x_5483_ = v___x_5480_;
                        v_isShared_5484_ = v_isSharedCheck_5500_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5481_);
                        lean_dec(v___x_5480_);
                        v___x_5483_ = lean_box(0);
                        v_isShared_5484_ = v_isSharedCheck_5500_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5477_);
                    lean_dec(v_snd_5475_);
                    v_a_5501_ = lean_ctor_get(v___x_5480_, 0);
                    v_isSharedCheck_5508_ = (!lean_is_exclusive(v___x_5480_)) as u8;
                    if v_isSharedCheck_5508_ == 0 {
                        v___x_5503_ = v___x_5480_;
                        v_isShared_5504_ = v_isSharedCheck_5508_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5501_);
                        lean_dec(v___x_5480_);
                        v___x_5503_ = lean_box(0);
                        v_isShared_5504_ = v_isSharedCheck_5508_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5481_) == 0 {
                    v___x_5485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5485_, 0, v_a_5481_);
                    if v_isShared_5478_ == 0 {
                        lean_ctor_set(v___x_5477_, 0, v___x_5485_);
                        v___x_5487_ = v___x_5477_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5485_);
                        lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_snd_5475_);
                        v___x_5487_ = v_reuseFailAlloc_5491_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5483_);
                    lean_dec(v_snd_5475_);
                    v_a_5492_ = lean_ctor_get(v_a_5481_, 0);
                    lean_inc(v_a_5492_);
                    lean_dec_ref_known(v_a_5481_, 1);
                    v___x_5493_ = lean_box(0);
                    if v_isShared_5478_ == 0 {
                        lean_ctor_set(v___x_5477_, 1, v_a_5492_);
                        lean_ctor_set(v___x_5477_, 0, v___x_5493_);
                        v___x_5495_ = v___x_5477_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5493_);
                        lean_ctor_set(v_reuseFailAlloc_5499_, 1, v_a_5492_);
                        v___x_5495_ = v_reuseFailAlloc_5499_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5484_ == 0 {
                    lean_ctor_set(v___x_5483_, 0, v___x_5487_);
                    v___x_5489_ = v___x_5483_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5487_);
                    v___x_5489_ = v_reuseFailAlloc_5490_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5489_;
            }
            5 => {
                v___x_5496_ = 1usize;
                v___x_5497_ = lean_usize_add(v_i_5466_, v___x_5496_);
                v_i_5466_ = v___x_5497_;
                v_b_5467_ = v___x_5495_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5504_ == 0 {
                    v___x_5506_ = v___x_5503_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
                    v___x_5506_ = v_reuseFailAlloc_5507_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_init_5511_: *mut LeanObject,
    mut v_as_5512_: *mut LeanObject,
    mut v_sz_5513_: *mut LeanObject,
    mut v_i_5514_: *mut LeanObject,
    mut v_b_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5521_: usize = 0;
    let mut v_i_boxed_5522_: usize = 0;
    let mut v_res_5523_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5521_ = lean_unbox_usize(v_sz_5513_);
    lean_dec(v_sz_5513_);
    v_i_boxed_5522_ = lean_unbox_usize(v_i_5514_);
    lean_dec(v_i_5514_);
    v_res_5523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__6(v_init_5511_, v_as_5512_, v_sz_boxed_5521_, v_i_boxed_5522_, v_b_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
    lean_dec(v___y_5519_);
    lean_dec_ref(v___y_5518_);
    lean_dec(v___y_5517_);
    lean_dec_ref(v___y_5516_);
    lean_dec_ref(v_as_5512_);
    lean_dec_ref(v_init_5511_);
    return v_res_5523_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2___boxed(
    mut v_init_5524_: *mut LeanObject,
    mut v_n_5525_: *mut LeanObject,
    mut v_b_5526_: *mut LeanObject,
    mut v___y_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5532_: *mut LeanObject = core::ptr::null_mut();
    v_res_5532_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2(v_init_5524_, v_n_5525_, v_b_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
    lean_dec(v___y_5530_);
    lean_dec_ref(v___y_5529_);
    lean_dec(v___y_5528_);
    lean_dec_ref(v___y_5527_);
    lean_dec_ref(v_n_5525_);
    lean_dec_ref(v_init_5524_);
    return v_res_5532_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9___redArg(
    mut v_as_5533_: *mut LeanObject,
    mut v_sz_5534_: usize,
    mut v_i_5535_: usize,
    mut v_b_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: usize = 0;
    let mut v___x_5550_: usize = 0;
    let mut v_reuseFailAlloc_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: u8 = 0;
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut v_unused_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5538_ = lean_usize_dec_lt(v_i_5535_, v_sz_5534_);
                if v___x_5538_ == 0 {
                    v___x_5539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5539_, 0, v_b_5536_);
                    return v___x_5539_;
                } else {
                    v_snd_5540_ = lean_ctor_get(v_b_5536_, 1);
                    v_isSharedCheck_5558_ = (!lean_is_exclusive(v_b_5536_)) as u8;
                    if v_isSharedCheck_5558_ == 0 {
                        v_unused_5559_ = lean_ctor_get(v_b_5536_, 0);
                        lean_dec(v_unused_5559_);
                        v___x_5542_ = v_b_5536_;
                        v_isShared_5543_ = v_isSharedCheck_5558_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5540_);
                        lean_dec(v_b_5536_);
                        v___x_5542_ = lean_box(0);
                        v_isShared_5543_ = v_isSharedCheck_5558_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5544_ = lean_box(0);
                v_a_5553_ = lean_array_uget_borrowed(v_as_5533_, v_i_5535_);
                if lean_obj_tag(v_a_5553_) == 0 {
                    v_a_5546_ = v_snd_5540_;
                    state = 2;
                    continue;
                } else {
                    v_val_5554_ = lean_ctor_get(v_a_5553_, 0);
                    v___x_5555_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5554_);
                    if v___x_5555_ == 0 {
                        lean_inc(v_val_5554_);
                        v___x_5556_ = l_Lean_LocalDecl_toExpr(v_val_5554_);
                        v___x_5557_ = lean_array_push(v_snd_5540_, v___x_5556_);
                        v_a_5546_ = v___x_5557_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5546_ = v_snd_5540_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5543_ == 0 {
                    lean_ctor_set(v___x_5542_, 1, v_a_5546_);
                    lean_ctor_set(v___x_5542_, 0, v___x_5544_);
                    v___x_5548_ = v___x_5542_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5552_, 0, v___x_5544_);
                    lean_ctor_set(v_reuseFailAlloc_5552_, 1, v_a_5546_);
                    v___x_5548_ = v_reuseFailAlloc_5552_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5549_ = 1usize;
                v___x_5550_ = lean_usize_add(v_i_5535_, v___x_5549_);
                v_i_5535_ = v___x_5550_;
                v_b_5536_ = v___x_5548_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9___redArg___boxed(
    mut v_as_5560_: *mut LeanObject,
    mut v_sz_5561_: *mut LeanObject,
    mut v_i_5562_: *mut LeanObject,
    mut v_b_5563_: *mut LeanObject,
    mut v___y_5564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5565_: usize = 0;
    let mut v_i_boxed_5566_: usize = 0;
    let mut v_res_5567_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5565_ = lean_unbox_usize(v_sz_5561_);
    lean_dec(v_sz_5561_);
    v_i_boxed_5566_ = lean_unbox_usize(v_i_5562_);
    lean_dec(v_i_5562_);
    v_res_5567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9___redArg(v_as_5560_, v_sz_boxed_5565_, v_i_boxed_5566_, v_b_5563_);
    lean_dec_ref(v_as_5560_);
    return v_res_5567_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3(
    mut v_as_5568_: *mut LeanObject,
    mut v_sz_5569_: usize,
    mut v_i_5570_: usize,
    mut v_b_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
    mut v___y_5573_: *mut LeanObject,
    mut v___y_5574_: *mut LeanObject,
    mut v___y_5575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5577_: u8 = 0;
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: usize = 0;
    let mut v___x_5589_: usize = 0;
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_unused_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5577_ = lean_usize_dec_lt(v_i_5570_, v_sz_5569_);
                if v___x_5577_ == 0 {
                    v___x_5578_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5578_, 0, v_b_5571_);
                    return v___x_5578_;
                } else {
                    v_snd_5579_ = lean_ctor_get(v_b_5571_, 1);
                    v_isSharedCheck_5597_ = (!lean_is_exclusive(v_b_5571_)) as u8;
                    if v_isSharedCheck_5597_ == 0 {
                        v_unused_5598_ = lean_ctor_get(v_b_5571_, 0);
                        lean_dec(v_unused_5598_);
                        v___x_5581_ = v_b_5571_;
                        v_isShared_5582_ = v_isSharedCheck_5597_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5579_);
                        lean_dec(v_b_5571_);
                        v___x_5581_ = lean_box(0);
                        v_isShared_5582_ = v_isSharedCheck_5597_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5583_ = lean_box(0);
                v_a_5592_ = lean_array_uget_borrowed(v_as_5568_, v_i_5570_);
                if lean_obj_tag(v_a_5592_) == 0 {
                    v_a_5585_ = v_snd_5579_;
                    state = 2;
                    continue;
                } else {
                    v_val_5593_ = lean_ctor_get(v_a_5592_, 0);
                    v___x_5594_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5593_);
                    if v___x_5594_ == 0 {
                        lean_inc(v_val_5593_);
                        v___x_5595_ = l_Lean_LocalDecl_toExpr(v_val_5593_);
                        v___x_5596_ = lean_array_push(v_snd_5579_, v___x_5595_);
                        v_a_5585_ = v___x_5596_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5585_ = v_snd_5579_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5582_ == 0 {
                    lean_ctor_set(v___x_5581_, 1, v_a_5585_);
                    lean_ctor_set(v___x_5581_, 0, v___x_5583_);
                    v___x_5587_ = v___x_5581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5583_);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_a_5585_);
                    v___x_5587_ = v_reuseFailAlloc_5591_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5588_ = 1usize;
                v___x_5589_ = lean_usize_add(v_i_5570_, v___x_5588_);
                v___x_5590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9___redArg(v_as_5568_, v_sz_5569_, v___x_5589_, v___x_5587_);
                return v___x_5590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3___boxed(
    mut v_as_5599_: *mut LeanObject,
    mut v_sz_5600_: *mut LeanObject,
    mut v_i_5601_: *mut LeanObject,
    mut v_b_5602_: *mut LeanObject,
    mut v___y_5603_: *mut LeanObject,
    mut v___y_5604_: *mut LeanObject,
    mut v___y_5605_: *mut LeanObject,
    mut v___y_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5608_: usize = 0;
    let mut v_i_boxed_5609_: usize = 0;
    let mut v_res_5610_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5608_ = lean_unbox_usize(v_sz_5600_);
    lean_dec(v_sz_5600_);
    v_i_boxed_5609_ = lean_unbox_usize(v_i_5601_);
    lean_dec(v_i_5601_);
    v_res_5610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3(v_as_5599_, v_sz_boxed_5608_, v_i_boxed_5609_, v_b_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
    lean_dec(v___y_5606_);
    lean_dec_ref(v___y_5605_);
    lean_dec(v___y_5604_);
    lean_dec_ref(v___y_5603_);
    lean_dec_ref(v_as_5599_);
    return v_res_5610_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0(
    mut v_t_5611_: *mut LeanObject,
    mut v_init_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5632_: usize = 0;
    let mut v___x_5633_: usize = 0;
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5638_: u8 = 0;
    let mut v_fst_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_a_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5652_: u8 = 0;
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5656_: u8 = 0;
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_a_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5661_: u8 = 0;
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5618_ = lean_ctor_get(v_t_5611_, 0);
                v_tail_5619_ = lean_ctor_get(v_t_5611_, 1);
                lean_inc_ref(v_init_5612_);
                v___x_5620_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2(v_init_5612_, v_root_5618_, v_init_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
                lean_dec_ref(v_init_5612_);
                if lean_obj_tag(v___x_5620_) == 0 {
                    v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
                    v_isSharedCheck_5657_ = (!lean_is_exclusive(v___x_5620_)) as u8;
                    if v_isSharedCheck_5657_ == 0 {
                        v___x_5623_ = v___x_5620_;
                        v_isShared_5624_ = v_isSharedCheck_5657_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5621_);
                        lean_dec(v___x_5620_);
                        v___x_5623_ = lean_box(0);
                        v_isShared_5624_ = v_isSharedCheck_5657_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5658_ = lean_ctor_get(v___x_5620_, 0);
                    v_isSharedCheck_5665_ = (!lean_is_exclusive(v___x_5620_)) as u8;
                    if v_isSharedCheck_5665_ == 0 {
                        v___x_5660_ = v___x_5620_;
                        v_isShared_5661_ = v_isSharedCheck_5665_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5658_);
                        lean_dec(v___x_5620_);
                        v___x_5660_ = lean_box(0);
                        v_isShared_5661_ = v_isSharedCheck_5665_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5621_) == 0 {
                    v_a_5625_ = lean_ctor_get(v_a_5621_, 0);
                    lean_inc(v_a_5625_);
                    lean_dec_ref_known(v_a_5621_, 1);
                    if v_isShared_5624_ == 0 {
                        lean_ctor_set(v___x_5623_, 0, v_a_5625_);
                        v___x_5627_ = v___x_5623_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5628_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5625_);
                        v___x_5627_ = v_reuseFailAlloc_5628_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5623_);
                    v_a_5629_ = lean_ctor_get(v_a_5621_, 0);
                    lean_inc(v_a_5629_);
                    lean_dec_ref_known(v_a_5621_, 1);
                    v___x_5630_ = lean_box(0);
                    v___x_5631_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5631_, 0, v___x_5630_);
                    lean_ctor_set(v___x_5631_, 1, v_a_5629_);
                    v_sz_5632_ = lean_array_size(v_tail_5619_);
                    v___x_5633_ = 0usize;
                    v___x_5634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3(v_tail_5619_, v_sz_5632_, v___x_5633_, v___x_5631_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
                    if lean_obj_tag(v___x_5634_) == 0 {
                        v_a_5635_ = lean_ctor_get(v___x_5634_, 0);
                        v_isSharedCheck_5648_ = (!lean_is_exclusive(v___x_5634_)) as u8;
                        if v_isSharedCheck_5648_ == 0 {
                            v___x_5637_ = v___x_5634_;
                            v_isShared_5638_ = v_isSharedCheck_5648_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5635_);
                            lean_dec(v___x_5634_);
                            v___x_5637_ = lean_box(0);
                            v_isShared_5638_ = v_isSharedCheck_5648_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5649_ = lean_ctor_get(v___x_5634_, 0);
                        v_isSharedCheck_5656_ = (!lean_is_exclusive(v___x_5634_)) as u8;
                        if v_isSharedCheck_5656_ == 0 {
                            v___x_5651_ = v___x_5634_;
                            v_isShared_5652_ = v_isSharedCheck_5656_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5649_);
                            lean_dec(v___x_5634_);
                            v___x_5651_ = lean_box(0);
                            v_isShared_5652_ = v_isSharedCheck_5656_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5627_;
            }
            3 => {
                v_fst_5639_ = lean_ctor_get(v_a_5635_, 0);
                if lean_obj_tag(v_fst_5639_) == 0 {
                    v_snd_5640_ = lean_ctor_get(v_a_5635_, 1);
                    lean_inc(v_snd_5640_);
                    lean_dec(v_a_5635_);
                    if v_isShared_5638_ == 0 {
                        lean_ctor_set(v___x_5637_, 0, v_snd_5640_);
                        v___x_5642_ = v___x_5637_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_snd_5640_);
                        v___x_5642_ = v_reuseFailAlloc_5643_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5639_);
                    lean_dec(v_a_5635_);
                    v_val_5644_ = lean_ctor_get(v_fst_5639_, 0);
                    lean_inc(v_val_5644_);
                    lean_dec_ref_known(v_fst_5639_, 1);
                    if v_isShared_5638_ == 0 {
                        lean_ctor_set(v___x_5637_, 0, v_val_5644_);
                        v___x_5646_ = v___x_5637_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_val_5644_);
                        v___x_5646_ = v_reuseFailAlloc_5647_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5642_;
            }
            5 => {
                return v___x_5646_;
            }
            6 => {
                if v_isShared_5652_ == 0 {
                    v___x_5654_ = v___x_5651_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
                    v___x_5654_ = v_reuseFailAlloc_5655_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5654_;
            }
            8 => {
                if v_isShared_5661_ == 0 {
                    v___x_5663_ = v___x_5660_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
                    v___x_5663_ = v_reuseFailAlloc_5664_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0___boxed(
    mut v_t_5666_: *mut LeanObject,
    mut v_init_5667_: *mut LeanObject,
    mut v___y_5668_: *mut LeanObject,
    mut v___y_5669_: *mut LeanObject,
    mut v___y_5670_: *mut LeanObject,
    mut v___y_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5673_: *mut LeanObject = core::ptr::null_mut();
    v_res_5673_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0(v_t_5666_, v_init_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
    lean_dec(v___y_5671_);
    lean_dec_ref(v___y_5670_);
    lean_dec(v___y_5669_);
    lean_dec_ref(v___y_5668_);
    lean_dec_ref(v_t_5666_);
    return v_res_5673_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0(
    mut v___y_5676_: *mut LeanObject,
    mut v___y_5677_: *mut LeanObject,
    mut v___y_5678_: *mut LeanObject,
    mut v___y_5679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hs_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_5681_ = lean_ctor_get(v___y_5676_, 2);
    v_decls_5682_ = lean_ctor_get(v_lctx_5681_, 1);
    v_hs_5683_ = l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0___closed__0;
    v___x_5684_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0(v_decls_5682_, v_hs_5683_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0___boxed(
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5690_: *mut LeanObject = core::ptr::null_mut();
    v_res_5690_ = l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0(
        v___y_5685_,
        v___y_5686_,
        v___y_5687_,
        v___y_5688_,
    );
    lean_dec(v___y_5688_);
    lean_dec_ref(v___y_5687_);
    lean_dec(v___y_5686_);
    lean_dec_ref(v___y_5685_);
    return v_res_5690_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_symmSaturate_spec__2(
    mut v_a_5691_: *mut LeanObject,
    mut v_as_5692_: *mut LeanObject,
    mut v_i_5693_: usize,
    mut v_stop_5694_: usize,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5700_: u8 = 0;
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5706_: u8 = 0;
    let mut v___x_5707_: u8 = 0;
    let mut v___x_5708_: usize = 0;
    let mut v___x_5709_: usize = 0;
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5714_: u8 = 0;
    let mut v___x_5715_: u8 = 0;
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5700_ = lean_usize_dec_eq(v_i_5693_, v_stop_5694_);
                if v___x_5700_ == 0 {
                    v___x_5701_ = lean_array_uget_borrowed(v_as_5692_, v_i_5693_);
                    lean_inc(v___x_5701_);
                    lean_inc_ref(v_a_5691_);
                    v___x_5702_ = l_Lean_Meta_isExprDefEq(
                        v_a_5691_,
                        v___x_5701_,
                        v___y_5695_,
                        v___y_5696_,
                        v___y_5697_,
                        v___y_5698_,
                    );
                    if lean_obj_tag(v___x_5702_) == 0 {
                        v_a_5703_ = lean_ctor_get(v___x_5702_, 0);
                        v_isSharedCheck_5714_ = (!lean_is_exclusive(v___x_5702_)) as u8;
                        if v_isSharedCheck_5714_ == 0 {
                            v___x_5705_ = v___x_5702_;
                            v_isShared_5706_ = v_isSharedCheck_5714_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5703_);
                            lean_dec(v___x_5702_);
                            v___x_5705_ = lean_box(0);
                            v_isShared_5706_ = v_isSharedCheck_5714_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_5691_);
                        return v___x_5702_;
                    }
                } else {
                    lean_dec_ref(v_a_5691_);
                    v___x_5715_ = 0;
                    v___x_5716_ = lean_box((v___x_5715_) as usize);
                    v___x_5717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5717_, 0, v___x_5716_);
                    return v___x_5717_;
                }
            }
            1 => {
                v___x_5707_ = (lean_unbox(v_a_5703_) as u8);
                if v___x_5707_ == 0 {
                    lean_del_object(v___x_5705_);
                    lean_dec(v_a_5703_);
                    v___x_5708_ = 1usize;
                    v___x_5709_ = lean_usize_add(v_i_5693_, v___x_5708_);
                    v_i_5693_ = v___x_5709_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_5691_);
                    if v_isShared_5706_ == 0 {
                        v___x_5712_ = v___x_5705_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_a_5703_);
                        v___x_5712_ = v_reuseFailAlloc_5713_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_symmSaturate_spec__2___boxed(
    mut v_a_5718_: *mut LeanObject,
    mut v_as_5719_: *mut LeanObject,
    mut v_i_5720_: *mut LeanObject,
    mut v_stop_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5727_: usize = 0;
    let mut v_stop_boxed_5728_: usize = 0;
    let mut v_res_5729_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5727_ = lean_unbox_usize(v_i_5720_);
    lean_dec(v_i_5720_);
    v_stop_boxed_5728_ = lean_unbox_usize(v_stop_5721_);
    lean_dec(v_stop_5721_);
    v_res_5729_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_symmSaturate_spec__2(v_a_5718_, v_as_5719_, v_i_boxed_5727_, v_stop_boxed_5728_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
    lean_dec(v___y_5725_);
    lean_dec_ref(v___y_5724_);
    lean_dec(v___y_5723_);
    lean_dec_ref(v___y_5722_);
    lean_dec_ref(v_as_5719_);
    return v_res_5729_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3(
    mut v_a_5731_: *mut LeanObject,
    mut v_as_5732_: *mut LeanObject,
    mut v_sz_5733_: usize,
    mut v_i_5734_: usize,
    mut v_b_5735_: *mut LeanObject,
    mut v___y_5736_: *mut LeanObject,
    mut v___y_5737_: *mut LeanObject,
    mut v___y_5738_: *mut LeanObject,
    mut v___y_5739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___y_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5748_: u8 = 0;
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: u8 = 0;
    let mut v___x_5753_: u8 = 0;
    let mut v___x_5754_: u8 = 0;
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5760_: u8 = 0;
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: usize = 0;
    let mut v___x_5778_: usize = 0;
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: u8 = 0;
    let mut v_a_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5754_ = lean_usize_dec_lt(v_i_5734_, v_sz_5733_);
                if v___x_5754_ == 0 {
                    v___x_5755_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5755_, 0, v_b_5735_);
                    return v___x_5755_;
                } else {
                    v_a_5756_ = lean_array_uget_borrowed(v_as_5732_, v_i_5734_);
                    lean_inc(v_a_5756_);
                    v___x_5757_ = l_Lean_Expr_applySymm(
                        v_a_5756_,
                        v___y_5736_,
                        v___y_5737_,
                        v___y_5738_,
                        v___y_5739_,
                    );
                    if lean_obj_tag(v___x_5757_) == 0 {
                        v_a_5758_ = lean_ctor_get(v___x_5757_, 0);
                        lean_inc_n(v_a_5758_, 2);
                        lean_dec_ref_known(v___x_5757_, 1);
                        lean_inc(v___y_5739_);
                        lean_inc_ref(v___y_5738_);
                        lean_inc(v___y_5737_);
                        lean_inc_ref(v___y_5736_);
                        v___x_5772_ = lean_infer_type(
                            v_a_5758_,
                            v___y_5736_,
                            v___y_5737_,
                            v___y_5738_,
                            v___y_5739_,
                        );
                        if lean_obj_tag(v___x_5772_) == 0 {
                            v_a_5773_ = lean_ctor_get(v___x_5772_, 0);
                            lean_inc(v_a_5773_);
                            lean_dec_ref_known(v___x_5772_, 1);
                            v___x_5774_ = lean_unsigned_to_nat(0);
                            v___x_5775_ = lean_array_get_size(v_a_5731_);
                            v___x_5776_ = lean_nat_dec_lt(v___x_5774_, v___x_5775_);
                            if v___x_5776_ == 0 {
                                lean_dec(v_a_5773_);
                                v_a_5760_ = v___x_5776_;
                                state = 4;
                                continue;
                            } else {
                                if v___x_5776_ == 0 {
                                    lean_dec(v_a_5773_);
                                    v_a_5760_ = v___x_5776_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_5777_ = 0usize;
                                    v___x_5778_ = lean_usize_of_nat(v___x_5775_);
                                    v___x_5779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_symmSaturate_spec__2(v_a_5773_, v_a_5731_, v___x_5777_, v___x_5778_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_);
                                    if lean_obj_tag(v___x_5779_) == 0 {
                                        v_a_5780_ = lean_ctor_get(v___x_5779_, 0);
                                        lean_inc(v_a_5780_);
                                        lean_dec_ref_known(v___x_5779_, 1);
                                        v___x_5781_ = (lean_unbox(v_a_5780_) as u8);
                                        lean_dec(v_a_5780_);
                                        v_a_5760_ = v___x_5781_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v_a_5758_);
                                        v_a_5782_ = lean_ctor_get(v___x_5779_, 0);
                                        lean_inc(v_a_5782_);
                                        lean_dec_ref_known(v___x_5779_, 1);
                                        v_a_5751_ = v_a_5782_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5758_);
                            v_a_5783_ = lean_ctor_get(v___x_5772_, 0);
                            lean_inc(v_a_5783_);
                            lean_dec_ref_known(v___x_5772_, 1);
                            v_a_5751_ = v_a_5783_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5784_ = lean_ctor_get(v___x_5757_, 0);
                        lean_inc(v_a_5784_);
                        lean_dec_ref_known(v___x_5757_, 1);
                        v_a_5751_ = v_a_5784_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5743_ = 1usize;
                v___x_5744_ = lean_usize_add(v_i_5734_, v___x_5743_);
                v_i_5734_ = v___x_5744_;
                v_b_5735_ = v_snd_5742_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_5748_ == 0 {
                    lean_dec_ref(v___y_5747_);
                    v_snd_5742_ = v_b_5735_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_b_5735_);
                    v___x_5749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5749_, 0, v___y_5747_);
                    return v___x_5749_;
                }
            }
            3 => {
                v___x_5752_ = l_Lean_Exception_isInterrupt(v_a_5751_);
                if v___x_5752_ == 0 {
                    lean_inc_ref(v_a_5751_);
                    v___x_5753_ = l_Lean_Exception_isRuntime(v_a_5751_);
                    v___y_5747_ = v_a_5751_;
                    v___y_5748_ = v___x_5753_;
                    state = 2;
                    continue;
                } else {
                    v___y_5747_ = v_a_5751_;
                    v___y_5748_ = v___x_5752_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_a_5760_ == 0 {
                    if v___x_5754_ == 0 {
                        lean_dec(v_a_5758_);
                        v_snd_5742_ = v_b_5735_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5761_ = l_Lean_Expr_fvarId_x21(v_a_5756_);
                        v___x_5762_ = l_Lean_FVarId_getUserName___redArg(
                            v___x_5761_,
                            v___y_5736_,
                            v___y_5738_,
                            v___y_5739_,
                        );
                        if lean_obj_tag(v___x_5762_) == 0 {
                            v_a_5763_ = lean_ctor_get(v___x_5762_, 0);
                            lean_inc(v_a_5763_);
                            lean_dec_ref_known(v___x_5762_, 1);
                            v___x_5764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3___closed__0;
                            v___x_5765_ = lean_name_append_after(v_a_5763_, v___x_5764_);
                            v___x_5766_ = lean_box(0);
                            lean_inc(v_b_5735_);
                            v___x_5767_ = l_Lean_MVarId_note(
                                v_b_5735_,
                                v___x_5765_,
                                v_a_5758_,
                                v___x_5766_,
                                v___y_5736_,
                                v___y_5737_,
                                v___y_5738_,
                                v___y_5739_,
                            );
                            if lean_obj_tag(v___x_5767_) == 0 {
                                lean_dec(v_b_5735_);
                                v_a_5768_ = lean_ctor_get(v___x_5767_, 0);
                                lean_inc(v_a_5768_);
                                lean_dec_ref_known(v___x_5767_, 1);
                                v_snd_5769_ = lean_ctor_get(v_a_5768_, 1);
                                lean_inc(v_snd_5769_);
                                lean_dec(v_a_5768_);
                                v_snd_5742_ = v_snd_5769_;
                                state = 1;
                                continue;
                            } else {
                                v_a_5770_ = lean_ctor_get(v___x_5767_, 0);
                                lean_inc(v_a_5770_);
                                lean_dec_ref_known(v___x_5767_, 1);
                                v_a_5751_ = v_a_5770_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5758_);
                            v_a_5771_ = lean_ctor_get(v___x_5762_, 0);
                            lean_inc(v_a_5771_);
                            lean_dec_ref_known(v___x_5762_, 1);
                            v_a_5751_ = v_a_5771_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5758_);
                    v_snd_5742_ = v_b_5735_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3___boxed(
    mut v_a_5785_: *mut LeanObject,
    mut v_as_5786_: *mut LeanObject,
    mut v_sz_5787_: *mut LeanObject,
    mut v_i_5788_: *mut LeanObject,
    mut v_b_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5795_: usize = 0;
    let mut v_i_boxed_5796_: usize = 0;
    let mut v_res_5797_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5795_ = lean_unbox_usize(v_sz_5787_);
    lean_dec(v_sz_5787_);
    v_i_boxed_5796_ = lean_unbox_usize(v_i_5788_);
    lean_dec(v_i_5788_);
    v_res_5797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3(v_a_5785_, v_as_5786_, v_sz_boxed_5795_, v_i_boxed_5796_, v_b_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
    lean_dec(v___y_5793_);
    lean_dec_ref(v___y_5792_);
    lean_dec(v___y_5791_);
    lean_dec_ref(v___y_5790_);
    lean_dec_ref(v_as_5786_);
    lean_dec_ref(v_a_5785_);
    return v_res_5797_;
}
pub unsafe fn l_Lean_MVarId_symmSaturate___lam__0(
    mut v_g_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5806_: usize = 0;
    let mut v___x_5807_: usize = 0;
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5814_: u8 = 0;
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5818_: u8 = 0;
    let mut v_a_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5822_: u8 = 0;
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5804_ = l_Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0(
                    v___y_5799_,
                    v___y_5800_,
                    v___y_5801_,
                    v___y_5802_,
                );
                if lean_obj_tag(v___x_5804_) == 0 {
                    v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
                    lean_inc_n(v_a_5805_, 2);
                    lean_dec_ref_known(v___x_5804_, 1);
                    v_sz_5806_ = lean_array_size(v_a_5805_);
                    v___x_5807_ = 0usize;
                    v___x_5808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_symmSaturate_spec__1(v_sz_5806_, v___x_5807_, v_a_5805_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
                    if lean_obj_tag(v___x_5808_) == 0 {
                        v_a_5809_ = lean_ctor_get(v___x_5808_, 0);
                        lean_inc(v_a_5809_);
                        lean_dec_ref_known(v___x_5808_, 1);
                        v___x_5810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_symmSaturate_spec__3(v_a_5809_, v_a_5805_, v_sz_5806_, v___x_5807_, v_g_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
                        lean_dec(v_a_5805_);
                        lean_dec(v_a_5809_);
                        return v___x_5810_;
                    } else {
                        lean_dec(v_a_5805_);
                        lean_dec(v_g_5798_);
                        v_a_5811_ = lean_ctor_get(v___x_5808_, 0);
                        v_isSharedCheck_5818_ = (!lean_is_exclusive(v___x_5808_)) as u8;
                        if v_isSharedCheck_5818_ == 0 {
                            v___x_5813_ = v___x_5808_;
                            v_isShared_5814_ = v_isSharedCheck_5818_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5811_);
                            lean_dec(v___x_5808_);
                            v___x_5813_ = lean_box(0);
                            v_isShared_5814_ = v_isSharedCheck_5818_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_g_5798_);
                    v_a_5819_ = lean_ctor_get(v___x_5804_, 0);
                    v_isSharedCheck_5826_ = (!lean_is_exclusive(v___x_5804_)) as u8;
                    if v_isSharedCheck_5826_ == 0 {
                        v___x_5821_ = v___x_5804_;
                        v_isShared_5822_ = v_isSharedCheck_5826_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5819_);
                        lean_dec(v___x_5804_);
                        v___x_5821_ = lean_box(0);
                        v_isShared_5822_ = v_isSharedCheck_5826_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5814_ == 0 {
                    v___x_5816_ = v___x_5813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
                    v___x_5816_ = v_reuseFailAlloc_5817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5816_;
            }
            3 => {
                if v_isShared_5822_ == 0 {
                    v___x_5824_ = v___x_5821_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5825_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5819_);
                    v___x_5824_ = v_reuseFailAlloc_5825_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_symmSaturate___lam__0___boxed(
    mut v_g_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
    mut v___y_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5833_: *mut LeanObject = core::ptr::null_mut();
    v_res_5833_ = l_Lean_MVarId_symmSaturate___lam__0(
        v_g_5827_,
        v___y_5828_,
        v___y_5829_,
        v___y_5830_,
        v___y_5831_,
    );
    lean_dec(v___y_5831_);
    lean_dec_ref(v___y_5830_);
    lean_dec(v___y_5829_);
    lean_dec_ref(v___y_5828_);
    return v_res_5833_;
}
pub unsafe fn l_Lean_MVarId_symmSaturate(
    mut v_g_5834_: *mut LeanObject,
    mut v_a_5835_: *mut LeanObject,
    mut v_a_5836_: *mut LeanObject,
    mut v_a_5837_: *mut LeanObject,
    mut v_a_5838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_g_5834_);
    v___f_5840_ = lean_alloc_closure(
        l_Lean_MVarId_symmSaturate___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5840_, 0, v_g_5834_);
    v___x_5841_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_symmSaturate_spec__4___redArg(
        v_g_5834_,
        v___f_5840_,
        v_a_5835_,
        v_a_5836_,
        v_a_5837_,
        v_a_5838_,
    );
    return v___x_5841_;
}
pub unsafe fn l_Lean_MVarId_symmSaturate___boxed(
    mut v_g_5842_: *mut LeanObject,
    mut v_a_5843_: *mut LeanObject,
    mut v_a_5844_: *mut LeanObject,
    mut v_a_5845_: *mut LeanObject,
    mut v_a_5846_: *mut LeanObject,
    mut v_a_5847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5848_: *mut LeanObject = core::ptr::null_mut();
    v_res_5848_ = l_Lean_MVarId_symmSaturate(v_g_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_);
    lean_dec(v_a_5846_);
    lean_dec_ref(v_a_5845_);
    lean_dec(v_a_5844_);
    lean_dec_ref(v_a_5843_);
    return v_res_5848_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9(
    mut v_as_5849_: *mut LeanObject,
    mut v_sz_5850_: usize,
    mut v_i_5851_: usize,
    mut v_b_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    v___x_5858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9___redArg(v_as_5849_, v_sz_5850_, v_i_5851_, v_b_5852_);
    return v___x_5858_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9___boxed(
    mut v_as_5859_: *mut LeanObject,
    mut v_sz_5860_: *mut LeanObject,
    mut v_i_5861_: *mut LeanObject,
    mut v_b_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
    mut v___y_5864_: *mut LeanObject,
    mut v___y_5865_: *mut LeanObject,
    mut v___y_5866_: *mut LeanObject,
    mut v___y_5867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5868_: usize = 0;
    let mut v_i_boxed_5869_: usize = 0;
    let mut v_res_5870_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5868_ = lean_unbox_usize(v_sz_5860_);
    lean_dec(v_sz_5860_);
    v_i_boxed_5869_ = lean_unbox_usize(v_i_5861_);
    lean_dec(v_i_5861_);
    v_res_5870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__3_spec__9(v_as_5859_, v_sz_boxed_5868_, v_i_boxed_5869_, v_b_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_);
    lean_dec(v___y_5866_);
    lean_dec_ref(v___y_5865_);
    lean_dec(v___y_5864_);
    lean_dec_ref(v___y_5863_);
    lean_dec_ref(v_as_5859_);
    return v_res_5870_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8(
    mut v_as_5871_: *mut LeanObject,
    mut v_sz_5872_: usize,
    mut v_i_5873_: usize,
    mut v_b_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    v___x_5880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8___redArg(v_as_5871_, v_sz_5872_, v_i_5873_, v_b_5874_);
    return v___x_5880_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8___boxed(
    mut v_as_5881_: *mut LeanObject,
    mut v_sz_5882_: *mut LeanObject,
    mut v_i_5883_: *mut LeanObject,
    mut v_b_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
    mut v___y_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
    mut v___y_5889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5890_: usize = 0;
    let mut v_i_boxed_5891_: usize = 0;
    let mut v_res_5892_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5890_ = lean_unbox_usize(v_sz_5882_);
    lean_dec(v_sz_5882_);
    v_i_boxed_5891_ = lean_unbox_usize(v_i_5883_);
    lean_dec(v_i_5883_);
    v_res_5892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_symmSaturate_spec__0_spec__0_spec__2_spec__7_spec__8(v_as_5881_, v_sz_boxed_5890_, v_i_boxed_5891_, v_b_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
    lean_dec(v___y_5888_);
    lean_dec_ref(v___y_5887_);
    lean_dec(v___y_5886_);
    lean_dec_ref(v___y_5885_);
    lean_dec_ref(v_as_5881_);
    return v_res_5892_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Symm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_1414739777____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Symm_symmExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Symm_symmExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn___regBuiltin___private_Lean_Meta_Tactic_Symm_0__Lean_Meta_Symm_initFn_docString__1_00___x40_Lean_Meta_Tactic_Symm_3447505512____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Symm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Symm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Symm(builtin);
}
