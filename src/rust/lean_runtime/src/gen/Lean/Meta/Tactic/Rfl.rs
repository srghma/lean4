// Lean compiler output
// Module: Lean.Meta.Tactic.Rfl
// Imports: Lean.Elab.Tactic.Basic Lean.Meta.Tactic.Refl
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop;
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_replaceRef,
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
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_goalsToMessageData,
    runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOf, l_Lean_Expr_isAppOfArity, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hint_x27, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_inlineExpr, l_Lean_inlineExprTrailing,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_MVarId_setType___redArg,
    l_Lean_MessageData_ofLazyM, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_isExprDefEqGuarded, l_Lean_Meta_mkConstWithFreshMVarLevels,
    l_Lean_Meta_saveState___redArg, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_addPPExplicitToExposeDiff;
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Main::{
    l_Lean_Meta_DiscrTree_getMatch___redArg, l_Lean_Meta_DiscrTree_mkPath,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::{l_Lean_MVarId_apply, l_Lean_MVarId_applyConst};
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType, l_Lean_MVarId_getType_x27,
    l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__1_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__1_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__1_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 102, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 102, 108, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,5419750890034921234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,3129550069451782643 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<94> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 91, m_data: [96, 91, 114, 101, 102, 108, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 111, 110, 108, 121, 32, 97, 112, 112, 108, 105, 101, 115, 32, 116, 111, 32, 108, 101, 109, 109, 97, 115, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 120, 32, 226, 136, 188, 32, 120, 96, 44, 32, 98, 117, 116, 32, 116, 104, 105, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 58, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [96, 91, 114, 101, 102, 108, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 109, 97, 121, 32, 110, 111, 116, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 96, 69, 113, 46, 114, 101, 102, 108, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,413001447997579943 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,11987862017545586202 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,18421195322054110651 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,9813174280525276627 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,6794247910720123127 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,8085156711961148742 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,4381271339048930295 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,6736287563197226122 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,6283973964088795950 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,13704910694629257171 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,15806089374918591223 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,((( 914023288 as usize) << 1) | 1) as *mut LeanObject,429630521333143166 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,17391090702610290601 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,13039367319386351169 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,559035813062002908 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,16107927835509634124 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [114, 101, 102, 108, 101, 120, 105, 118, 105, 116, 121, 32, 114, 101, 108, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__30_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__30_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__30_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__31_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__30_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__31_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__31_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value: LeanStringObject<282> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 282, m_capacity: 282, m_length: 281, m_data: [84, 97, 103, 115, 32, 114, 101, 102, 108, 101, 120, 105, 118, 105, 116, 121, 32, 108, 101, 109, 109, 97, 115, 32, 116, 111, 32, 98, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 96, 114, 102, 108, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 65, 32, 114, 101, 102, 108, 101, 120, 105, 118, 105, 116, 121, 32, 108, 101, 109, 109, 97, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 96, 114, 32, 120, 32, 120, 96, 32, 119, 104, 101, 114, 101, 32, 96, 114, 96, 32, 105, 115, 32, 97, 110, 32, 97, 114, 98, 105, 116, 114, 97, 114, 121, 32, 114, 101, 108, 97, 116, 105, 111, 110, 46, 10, 10, 73, 116, 32, 105, 115, 32, 110, 111, 116, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 116, 97, 103, 32, 114, 101, 102, 108, 101, 120, 105, 118, 105, 116, 121, 32, 108, 101, 109, 109, 97, 115, 32, 102, 111, 114, 32, 96, 61, 96, 32, 117, 115, 105, 110, 103, 32, 116, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 46, 32, 84, 104, 101, 115, 101, 32, 97, 114, 101, 32, 104, 97, 110, 100, 108, 101, 100, 32, 97, 115, 32, 97, 10, 115, 112, 101, 99, 105, 97, 108, 32, 99, 97, 115, 101, 32, 105, 110, 32, 116, 104, 101, 32, 96, 114, 102, 108, 96, 32, 116, 97, 99, 116, 105, 99, 46, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__0___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            84, 104, 101, 32, 108, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyRfl___lam__0___closed__2_value: LeanStringObject<52> =
    LeanStringObject {
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
            10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32,
            114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,5416787921777642938 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__2_value) as *mut LeanObject,9395822403686643539 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__4_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 32, 103, 111, 97, 108, 115, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__6_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [114, 102, 108, 0],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__2_value) as *mut LeanObject,
        17342663138809293389 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__4_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            78, 111, 32, 96, 91, 114, 101, 102, 108, 93, 96, 32, 108, 101, 109, 109, 97, 32, 114,
            101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 102, 111, 114, 32, 114, 101, 108, 97,
            116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__4_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyRfl___lam__1___closed__6_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            65, 100, 100, 32, 116, 104, 101, 32, 96, 91, 114, 101, 102, 108, 93, 96, 32, 97, 116,
            116, 114, 105, 98, 117, 116, 101, 32, 116, 111, 32, 114, 101, 102, 108, 101, 120, 105,
            118, 105, 116, 121, 32, 108, 101, 109, 109, 97, 115, 32, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__6_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__1___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyRfl___lam__1___closed__8_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            116, 111, 32, 117, 115, 101, 32, 116, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__8_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__1___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__9: *mut LeanObject = core::ptr::null_mut();
static l_Lean_MVarId_applyRfl___lam__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
pub static l_Lean_MVarId_applyRfl___lam__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,13480818501600609864 as *mut LeanObject] };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__10_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__11_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [72, 69, 113, 0],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__11_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__11_value) as *mut LeanObject,
        13589827700912665667 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__12_value) as *mut LeanObject;
static l_Lean_MVarId_applyRfl___lam__1___closed__13_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__11_value)
                as *mut LeanObject,
            13589827700912665667 as *mut LeanObject,
        ],
    };
pub static l_Lean_MVarId_applyRfl___lam__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__value) as *mut LeanObject,2990354745633524404 as *mut LeanObject] };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__13_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__14_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777472 as *mut LeanObject],
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_MVarId_applyRfl___lam__1___closed__15_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32,
            116, 111, 32, 98, 101, 32, 97, 32, 98, 105, 110, 97, 114, 121, 32, 114, 101, 108, 97,
            116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__15_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyRfl___lam__1___closed__17_value: LeanStringObject<77> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 77,
        m_capacity: 77,
        m_length: 76,
        m_data: [
            82, 101, 102, 108, 101, 120, 105, 118, 105, 116, 121, 32, 116, 97, 99, 116, 105, 99,
            115, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32,
            111, 110, 32, 103, 111, 97, 108, 115, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111,
            114, 109, 32, 96, 120, 32, 126, 32, 120, 96, 32, 111, 114, 32, 96, 82, 32, 120, 32,
            120, 96, 0,
        ],
    };
static mut l_Lean_MVarId_applyRfl___lam__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRfl___lam__1___closed__17_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyRfl___lam__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_applyRfl___lam__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_applyRfl___lam__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_applyRfl___lam__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyRfl___lam__1___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [114, 101, 108, 95, 111, 102, 95, 101, 113, 95, 97, 110, 100, 95, 114, 101, 102, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__value) as *mut LeanObject,5419750890034921234 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__0_value) as *mut LeanObject,2839855941779146049 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_MVarId_liftReflToEq___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [108, 105, 102, 116, 82, 101, 102, 108, 84, 111, 69, 113, 0],
};
static mut l_Lean_MVarId_liftReflToEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_liftReflToEq___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_liftReflToEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_liftReflToEq___closed__0_value) as *mut LeanObject,
        7848288902764961336 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_liftReflToEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_liftReflToEq___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_(
    mut v_x_2798_: *mut LeanObject,
    mut v_a_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    v___x_2800_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2800_, 0, v_a_2799_);
    lean_inc_ref_n(v___x_2800_, 2);
    v___x_2801_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2801_, 0, v___x_2800_);
    lean_ctor_set(v___x_2801_, 1, v___x_2800_);
    lean_ctor_set(v___x_2801_, 2, v___x_2800_);
    return v___x_2801_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2____boxed(
    mut v_x_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2804_: *mut LeanObject = core::ptr::null_mut();
    v_res_2804_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_(v_x_2802_, v_a_2803_);
    lean_dec_ref(v_x_2802_);
    return v_res_2804_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_2805_: *mut LeanObject,
    mut v_vals_2806_: *mut LeanObject,
    mut v_i_2807_: *mut LeanObject,
    mut v_k_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: u8 = 0;
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2809_ = lean_array_get_size(v_keys_2805_);
                v___x_2810_ = lean_nat_dec_lt(v_i_2807_, v___x_2809_);
                if v___x_2810_ == 0 {
                    lean_dec(v_i_2807_);
                    v___x_2811_ = lean_box(0);
                    return v___x_2811_;
                } else {
                    v_k_x27_2812_ = lean_array_fget_borrowed(v_keys_2805_, v_i_2807_);
                    v___x_2813_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2808_, v_k_x27_2812_);
                    if v___x_2813_ == 0 {
                        v___x_2814_ = lean_unsigned_to_nat(1);
                        v___x_2815_ = lean_nat_add(v_i_2807_, v___x_2814_);
                        lean_dec(v_i_2807_);
                        v_i_2807_ = v___x_2815_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2817_ = lean_array_fget_borrowed(v_vals_2806_, v_i_2807_);
                        lean_dec(v_i_2807_);
                        lean_inc(v___x_2817_);
                        v___x_2818_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2818_, 0, v___x_2817_);
                        return v___x_2818_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_2819_: *mut LeanObject,
    mut v_vals_2820_: *mut LeanObject,
    mut v_i_2821_: *mut LeanObject,
    mut v_k_2822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2823_: *mut LeanObject = core::ptr::null_mut();
    v_res_2823_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2819_, v_vals_2820_, v_i_2821_, v_k_2822_);
    lean_dec(v_k_2822_);
    lean_dec_ref(v_vals_2820_);
    lean_dec_ref(v_keys_2819_);
    return v_res_2823_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2824_: usize = 0;
    let mut v___x_2825_: usize = 0;
    let mut v___x_2826_: usize = 0;
    v___x_2824_ = 5usize;
    v___x_2825_ = 1usize;
    v___x_2826_ = lean_usize_shift_left(v___x_2825_, v___x_2824_);
    return v___x_2826_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2827_: usize = 0;
    let mut v___x_2828_: usize = 0;
    let mut v___x_2829_: usize = 0;
    v___x_2827_ = 1usize;
    v___x_2828_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2829_ = lean_usize_sub(v___x_2828_, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_2830_: *mut LeanObject,
    mut v_x_2831_: usize,
    mut v_x_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: usize = 0;
    let mut v___x_2836_: usize = 0;
    let mut v___x_2837_: usize = 0;
    let mut v_j_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: usize = 0;
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2830_) == 0 {
                    v_es_2833_ = lean_ctor_get(v_x_2830_, 0);
                    v___x_2834_ = lean_box(2);
                    v___x_2835_ = 5usize;
                    v___x_2836_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2837_ = lean_usize_land(v_x_2831_, v___x_2836_);
                    v_j_2838_ = lean_usize_to_nat(v___x_2837_);
                    v___x_2839_ = lean_array_get_borrowed(v___x_2834_, v_es_2833_, v_j_2838_);
                    lean_dec(v_j_2838_);
                    match lean_obj_tag(v___x_2839_) {
                        0 => {
                            v_key_2840_ = lean_ctor_get(v___x_2839_, 0);
                            v_val_2841_ = lean_ctor_get(v___x_2839_, 1);
                            v___x_2842_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2832_, v_key_2840_);
                            if v___x_2842_ == 0 {
                                v___x_2843_ = lean_box(0);
                                return v___x_2843_;
                            } else {
                                lean_inc(v_val_2841_);
                                v___x_2844_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2844_, 0, v_val_2841_);
                                return v___x_2844_;
                            }
                        }
                        1 => {
                            v_node_2845_ = lean_ctor_get(v___x_2839_, 0);
                            v___x_2846_ = lean_usize_shift_right(v_x_2831_, v___x_2835_);
                            v_x_2830_ = v_node_2845_;
                            v_x_2831_ = v___x_2846_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2848_ = lean_box(0);
                            return v___x_2848_;
                        }
                    }
                } else {
                    v_ks_2849_ = lean_ctor_get(v_x_2830_, 0);
                    v_vs_2850_ = lean_ctor_get(v_x_2830_, 1);
                    v___x_2851_ = lean_unsigned_to_nat(0);
                    v___x_2852_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2849_, v_vs_2850_, v___x_2851_, v_x_2832_);
                    return v___x_2852_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2853_: *mut LeanObject,
    mut v_x_2854_: *mut LeanObject,
    mut v_x_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1591__boxed_2856_: usize = 0;
    let mut v_res_2857_: *mut LeanObject = core::ptr::null_mut();
    v_x_1591__boxed_2856_ = lean_unbox_usize(v_x_2854_);
    lean_dec(v_x_2854_);
    v_res_2857_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2853_, v_x_1591__boxed_2856_, v_x_2855_);
    lean_dec(v_x_2855_);
    lean_dec_ref(v_x_2853_);
    return v_res_2857_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_2858_: *mut LeanObject,
    mut v_x_2859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2860_: u64 = 0;
    let mut v___x_2861_: usize = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    v___x_2860_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2859_);
    v___x_2861_ = lean_uint64_to_usize(v___x_2860_);
    v___x_2862_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2858_, v___x_2861_, v_x_2859_);
    return v___x_2862_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_2863_: *mut LeanObject,
    mut v_x_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2865_: *mut LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2863_, v_x_2864_);
    lean_dec(v_x_2864_);
    lean_dec_ref(v_x_2863_);
    return v_res_2865_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    v___x_2866_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
    return v___x_2866_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3(
    mut v_msg_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    v___x_2868_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0);
    v___x_2869_ = lean_panic_fn_borrowed(v___x_2868_, v_msg_2867_);
    return v___x_2869_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(
    mut v_x_2870_: *mut LeanObject,
    mut v_keys_2871_: *mut LeanObject,
    mut v_v_2872_: *mut LeanObject,
    mut v_k_2873_: *mut LeanObject,
    mut v_x_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    v___x_2875_ = lean_unsigned_to_nat(1);
    v___x_2876_ = lean_nat_add(v_x_2870_, v___x_2875_);
    v_c_2877_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        lean_box(0),
        v_keys_2871_,
        v_v_2872_,
        v___x_2876_,
    );
    lean_dec(v___x_2876_);
    v___x_2878_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2878_, 0, v_k_2873_);
    lean_ctor_set(v___x_2878_, 1, v_c_2877_);
    return v___x_2878_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(
    mut v_x_2879_: *mut LeanObject,
    mut v_keys_2880_: *mut LeanObject,
    mut v_v_2881_: *mut LeanObject,
    mut v_k_2882_: *mut LeanObject,
    mut v_x_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2884_: *mut LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2879_, v_keys_2880_, v_v_2881_, v_k_2882_, v_x_2883_);
    lean_dec_ref(v_keys_2880_);
    lean_dec(v_x_2879_);
    return v_res_2884_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(
    mut v_a_2885_: *mut LeanObject,
    mut v_b_2886_: *mut LeanObject,
) -> u8 {
    let mut v_fst_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    v_fst_2887_ = lean_ctor_get(v_a_2885_, 0);
    v_fst_2888_ = lean_ctor_get(v_b_2886_, 0);
    v___x_2889_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2887_, v_fst_2888_);
    return v___x_2889_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(
    mut v_a_2890_: *mut LeanObject,
    mut v_b_2891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2892_: u8 = 0;
    let mut v_r_2893_: *mut LeanObject = core::ptr::null_mut();
    v_res_2892_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_a_2890_, v_b_2891_);
    lean_dec_ref(v_b_2891_);
    lean_dec_ref(v_a_2890_);
    v_r_2893_ = lean_box((v_res_2892_) as usize);
    return v_r_2893_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(
    mut v_vs_2894_: *mut LeanObject,
    mut v_v_2895_: *mut LeanObject,
    mut v_i_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2897_ = lean_array_get_size(v_vs_2894_);
                v___x_2898_ = lean_nat_dec_lt(v_i_2896_, v___x_2897_);
                if v___x_2898_ == 0 {
                    lean_dec(v_i_2896_);
                    v___x_2899_ = lean_array_push(v_vs_2894_, v_v_2895_);
                    return v___x_2899_;
                } else {
                    v___x_2900_ = lean_array_fget_borrowed(v_vs_2894_, v_i_2896_);
                    v___x_2901_ = lean_name_eq(v_v_2895_, v___x_2900_);
                    if v___x_2901_ == 0 {
                        v___x_2902_ = lean_unsigned_to_nat(1);
                        v___x_2903_ = lean_nat_add(v_i_2896_, v___x_2902_);
                        lean_dec(v_i_2896_);
                        v_i_2896_ = v___x_2903_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2905_ = lean_array_fset(v_vs_2894_, v_i_2896_, v_v_2895_);
                        lean_dec(v_i_2896_);
                        return v___x_2905_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__5(
    mut v_vs_2906_: *mut LeanObject,
    mut v_v_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v___x_2908_ = lean_unsigned_to_nat(0);
    v___x_2909_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__10(v_vs_2906_, v_v_2907_, v___x_2908_);
    return v___x_2909_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_x_2914_: *mut LeanObject,
    mut v_keys_2915_: *mut LeanObject,
    mut v_v_2916_: *mut LeanObject,
    mut v_k_2917_: *mut LeanObject,
    mut v_as_2918_: *mut LeanObject,
    mut v_k_2919_: *mut LeanObject,
    mut v_x_2920_: *mut LeanObject,
    mut v_x_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_midVal_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v_snd_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2933_: u8 = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_unused_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u8 = 0;
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2922_ = lean_nat_add(v_x_2920_, v_x_2921_);
                v___x_2923_ = lean_unsigned_to_nat(1);
                v_mid_2924_ = lean_nat_shiftr(v___x_2922_, v___x_2923_);
                lean_dec(v___x_2922_);
                v_midVal_2925_ = lean_array_fget(v_as_2918_, v_mid_2924_);
                v___x_2926_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_midVal_2925_, v_k_2919_);
                if v___x_2926_ == 0 {
                    lean_dec(v_x_2921_);
                    v___x_2927_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_2919_, v_midVal_2925_);
                    if v___x_2927_ == 0 {
                        lean_dec(v_x_2920_);
                        v___x_2928_ = lean_array_get_size(v_as_2918_);
                        v___x_2929_ = lean_nat_dec_lt(v_mid_2924_, v___x_2928_);
                        if v___x_2929_ == 0 {
                            lean_dec(v_midVal_2925_);
                            lean_dec(v_mid_2924_);
                            lean_dec(v_k_2917_);
                            lean_dec(v_v_2916_);
                            return v_as_2918_;
                        } else {
                            v_snd_2930_ = lean_ctor_get(v_midVal_2925_, 1);
                            v_isSharedCheck_2942_ = (!lean_is_exclusive(v_midVal_2925_)) as u8;
                            if v_isSharedCheck_2942_ == 0 {
                                v_unused_2943_ = lean_ctor_get(v_midVal_2925_, 0);
                                lean_dec(v_unused_2943_);
                                v___x_2932_ = v_midVal_2925_;
                                v_isShared_2933_ = v_isSharedCheck_2942_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_2930_);
                                lean_dec(v_midVal_2925_);
                                v___x_2932_ = lean_box(0);
                                v_isShared_2933_ = v_isSharedCheck_2942_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_midVal_2925_);
                        v_x_2921_ = v_mid_2924_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_midVal_2925_);
                    v___x_2945_ = lean_nat_dec_eq(v_mid_2924_, v_x_2920_);
                    if v___x_2945_ == 0 {
                        lean_dec(v_x_2920_);
                        v_x_2920_ = v_mid_2924_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mid_2924_);
                        lean_dec(v_x_2921_);
                        v___x_2947_ = lean_nat_add(v_x_2914_, v___x_2923_);
                        v_c_2948_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_2915_, v_v_2916_, v___x_2947_);
                        lean_dec(v___x_2947_);
                        v___x_2949_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2949_, 0, v_k_2917_);
                        lean_ctor_set(v___x_2949_, 1, v_c_2948_);
                        v___x_2950_ = lean_nat_add(v_x_2920_, v___x_2923_);
                        lean_dec(v_x_2920_);
                        v_j_2951_ = lean_array_get_size(v_as_2918_);
                        v_as_2952_ = lean_array_push(v_as_2918_, v___x_2949_);
                        v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            lean_box(0),
                            v___x_2950_,
                            v_as_2952_,
                            v_j_2951_,
                        );
                        lean_dec(v___x_2950_);
                        return v___x_2953_;
                    }
                }
            }
            1 => {
                v___x_2934_ = lean_box(0);
                v_xs_x27_2935_ = lean_array_fset(v_as_2918_, v_mid_2924_, v___x_2934_);
                v___x_2936_ = lean_nat_add(v_x_2914_, v___x_2923_);
                v_c_2937_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2(v_keys_2915_, v_v_2916_, v___x_2936_, v_snd_2930_);
                lean_dec(v___x_2936_);
                if v_isShared_2933_ == 0 {
                    lean_ctor_set(v___x_2932_, 1, v_c_2937_);
                    lean_ctor_set(v___x_2932_, 0, v_k_2917_);
                    v___x_2939_ = v___x_2932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_k_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_c_2937_);
                    v___x_2939_ = v_reuseFailAlloc_2941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2940_ = lean_array_fset(v_xs_x27_2935_, v_mid_2924_, v___x_2939_);
                lean_dec(v_mid_2924_);
                return v___x_2940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6(
    mut v_x_2954_: *mut LeanObject,
    mut v_keys_2955_: *mut LeanObject,
    mut v_v_2956_: *mut LeanObject,
    mut v_k_2957_: *mut LeanObject,
    mut v_as_2958_: *mut LeanObject,
    mut v_k_2959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    v___x_2960_ = lean_array_get_size(v_as_2958_);
    v___x_2961_ = lean_unsigned_to_nat(0);
    v___x_2962_ = lean_nat_dec_eq(v___x_2960_, v___x_2961_);
    if v___x_2962_ == 0 {
        let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2964_: u8 = 0;
        v___x_2963_ = lean_array_fget_borrowed(v_as_2958_, v___x_2961_);
        v___x_2964_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_2959_, v___x_2963_);
        if v___x_2964_ == 0 {
            let mut v___x_2965_: u8 = 0;
            v___x_2965_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_2963_, v_k_2959_);
            if v___x_2965_ == 0 {
                let mut v___x_2966_: u8 = 0;
                v___x_2966_ = lean_nat_dec_lt(v___x_2961_, v___x_2960_);
                if v___x_2966_ == 0 {
                    lean_dec(v_k_2957_);
                    lean_dec(v_v_2956_);
                    return v_as_2958_;
                } else {
                    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_2968_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v___x_2963_);
                    v___x_2967_ = lean_box(0);
                    v_xs_x27_2968_ = lean_array_fset(v_as_2958_, v___x_2961_, v___x_2967_);
                    v___x_2969_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_2954_, v_keys_2955_, v_v_2956_, v_k_2957_, v___x_2963_);
                    v___x_2970_ = lean_array_fset(v_xs_x27_2968_, v___x_2961_, v___x_2969_);
                    return v___x_2970_;
                }
            } else {
                let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2974_: u8 = 0;
                v___x_2971_ = lean_unsigned_to_nat(1);
                v___x_2972_ = lean_nat_sub(v___x_2960_, v___x_2971_);
                v___x_2973_ = lean_array_fget_borrowed(v_as_2958_, v___x_2972_);
                v___x_2974_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_2973_, v_k_2959_);
                if v___x_2974_ == 0 {
                    let mut v___x_2975_: u8 = 0;
                    v___x_2975_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_2959_, v___x_2973_);
                    if v___x_2975_ == 0 {
                        let mut v___x_2976_: u8 = 0;
                        v___x_2976_ = lean_nat_dec_lt(v___x_2972_, v___x_2960_);
                        if v___x_2976_ == 0 {
                            lean_dec(v___x_2972_);
                            lean_dec(v_k_2957_);
                            lean_dec(v_v_2956_);
                            return v_as_2958_;
                        } else {
                            let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_xs_x27_2978_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
                            lean_inc(v___x_2973_);
                            v___x_2977_ = lean_box(0);
                            v_xs_x27_2978_ = lean_array_fset(v_as_2958_, v___x_2972_, v___x_2977_);
                            v___x_2979_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_2954_, v_keys_2955_, v_v_2956_, v_k_2957_, v___x_2973_);
                            v___x_2980_ = lean_array_fset(v_xs_x27_2978_, v___x_2972_, v___x_2979_);
                            lean_dec(v___x_2972_);
                            return v___x_2980_;
                        }
                    } else {
                        let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2981_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_2954_, v_keys_2955_, v_v_2956_, v_k_2957_, v_as_2958_, v_k_2959_, v___x_2961_, v___x_2972_);
                        return v___x_2981_;
                    }
                } else {
                    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_2972_);
                    v___x_2982_ = lean_box(0);
                    v___x_2983_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2954_, v_keys_2955_, v_v_2956_, v_k_2957_, v___x_2982_);
                    v___x_2984_ = lean_array_push(v_as_2958_, v___x_2983_);
                    return v___x_2984_;
                }
            }
        } else {
            let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
            let mut v_as_2987_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
            v___x_2985_ = lean_box(0);
            v___x_2986_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2954_, v_keys_2955_, v_v_2956_, v_k_2957_, v___x_2985_);
            v_as_2987_ = lean_array_push(v_as_2958_, v___x_2986_);
            v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                lean_box(0),
                v___x_2961_,
                v_as_2987_,
                v___x_2960_,
            );
            return v___x_2988_;
        }
    } else {
        let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
        v___x_2989_ = lean_box(0);
        v___x_2990_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2954_, v_keys_2955_, v_v_2956_, v_k_2957_, v___x_2989_);
        v___x_2991_ = lean_array_push(v_as_2958_, v___x_2990_);
        return v___x_2991_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2(
    mut v_keys_2992_: *mut LeanObject,
    mut v_v_2993_: *mut LeanObject,
    mut v_x_2994_: *mut LeanObject,
    mut v_x_2995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_2996_ = lean_ctor_get(v_x_2995_, 0);
                v_children_2997_ = lean_ctor_get(v_x_2995_, 1);
                v_isSharedCheck_3014_ = (!lean_is_exclusive(v_x_2995_)) as u8;
                if v_isSharedCheck_3014_ == 0 {
                    v___x_2999_ = v_x_2995_;
                    v_isShared_3000_ = v_isSharedCheck_3014_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_2997_);
                    lean_inc(v_vs_2996_);
                    lean_dec(v_x_2995_);
                    v___x_2999_ = lean_box(0);
                    v_isShared_3000_ = v_isSharedCheck_3014_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3001_ = lean_array_get_size(v_keys_2992_);
                v___x_3002_ = lean_nat_dec_lt(v_x_2994_, v___x_3001_);
                if v___x_3002_ == 0 {
                    v___x_3003_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_vs_2996_, v_v_2993_);
                    if v_isShared_3000_ == 0 {
                        lean_ctor_set(v___x_2999_, 0, v___x_3003_);
                        v___x_3005_ = v___x_2999_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_children_2997_);
                        v___x_3005_ = v_reuseFailAlloc_3006_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_3007_ = lean_array_fget_borrowed(v_keys_2992_, v_x_2994_);
                    v___x_3008_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___closed__1;
                    lean_inc_n(v_k_3007_, 2);
                    v___x_3009_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3009_, 0, v_k_3007_);
                    lean_ctor_set(v___x_3009_, 1, v___x_3008_);
                    v_c_3010_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_2994_, v_keys_2992_, v_v_2993_, v_k_3007_, v_children_2997_, v___x_3009_);
                    lean_dec_ref_known(v___x_3009_, 2);
                    if v_isShared_3000_ == 0 {
                        lean_ctor_set(v___x_2999_, 1, v_c_3010_);
                        v___x_3012_ = v___x_2999_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_vs_2996_);
                        lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_c_3010_);
                        v___x_3012_ = v_reuseFailAlloc_3013_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3005_;
            }
            3 => {
                return v___x_3012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(
    mut v_x_3015_: *mut LeanObject,
    mut v_keys_3016_: *mut LeanObject,
    mut v_v_3017_: *mut LeanObject,
    mut v_k_3018_: *mut LeanObject,
    mut v_x_3019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v_unused_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3020_ = lean_ctor_get(v_x_3019_, 1);
                v_isSharedCheck_3030_ = (!lean_is_exclusive(v_x_3019_)) as u8;
                if v_isSharedCheck_3030_ == 0 {
                    v_unused_3031_ = lean_ctor_get(v_x_3019_, 0);
                    lean_dec(v_unused_3031_);
                    v___x_3022_ = v_x_3019_;
                    v_isShared_3023_ = v_isSharedCheck_3030_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3020_);
                    lean_dec(v_x_3019_);
                    v___x_3022_ = lean_box(0);
                    v_isShared_3023_ = v_isSharedCheck_3030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3024_ = lean_unsigned_to_nat(1);
                v___x_3025_ = lean_nat_add(v_x_3015_, v___x_3024_);
                v_c_3026_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2(v_keys_3016_, v_v_3017_, v___x_3025_, v_snd_3020_);
                lean_dec(v___x_3025_);
                if v_isShared_3023_ == 0 {
                    lean_ctor_set(v___x_3022_, 1, v_c_3026_);
                    lean_ctor_set(v___x_3022_, 0, v_k_3018_);
                    v___x_3028_ = v___x_3022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_k_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_c_3026_);
                    v___x_3028_ = v_reuseFailAlloc_3029_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(
    mut v_x_3032_: *mut LeanObject,
    mut v_keys_3033_: *mut LeanObject,
    mut v_v_3034_: *mut LeanObject,
    mut v_k_3035_: *mut LeanObject,
    mut v_x_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3037_: *mut LeanObject = core::ptr::null_mut();
    v_res_3037_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_3032_, v_keys_3033_, v_v_3034_, v_k_3035_, v_x_3036_);
    lean_dec_ref(v_keys_3033_);
    lean_dec(v_x_3032_);
    return v_res_3037_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2___boxed(
    mut v_keys_3038_: *mut LeanObject,
    mut v_v_3039_: *mut LeanObject,
    mut v_x_3040_: *mut LeanObject,
    mut v_x_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2(v_keys_3038_, v_v_3039_, v_x_3040_, v_x_3041_);
    lean_dec(v_x_3040_);
    lean_dec_ref(v_keys_3038_);
    return v_res_3042_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_x_3043_: *mut LeanObject,
    mut v_keys_3044_: *mut LeanObject,
    mut v_v_3045_: *mut LeanObject,
    mut v_k_3046_: *mut LeanObject,
    mut v_as_3047_: *mut LeanObject,
    mut v_k_3048_: *mut LeanObject,
    mut v_x_3049_: *mut LeanObject,
    mut v_x_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3051_: *mut LeanObject = core::ptr::null_mut();
    v_res_3051_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_3043_, v_keys_3044_, v_v_3045_, v_k_3046_, v_as_3047_, v_k_3048_, v_x_3049_, v_x_3050_);
    lean_dec_ref(v_k_3048_);
    lean_dec_ref(v_keys_3044_);
    lean_dec(v_x_3043_);
    return v_res_3051_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(
    mut v_x_3052_: *mut LeanObject,
    mut v_keys_3053_: *mut LeanObject,
    mut v_v_3054_: *mut LeanObject,
    mut v_k_3055_: *mut LeanObject,
    mut v_as_3056_: *mut LeanObject,
    mut v_k_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3058_: *mut LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_3052_, v_keys_3053_, v_v_3054_, v_k_3055_, v_as_3056_, v_k_3057_);
    lean_dec_ref(v_k_3057_);
    lean_dec_ref(v_keys_3053_);
    lean_dec(v_x_3052_);
    return v_res_3058_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_x_3059_: *mut LeanObject,
    mut v_x_3060_: *mut LeanObject,
    mut v_x_3061_: *mut LeanObject,
    mut v_x_3062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3063_ = lean_ctor_get(v_x_3059_, 0);
                v_vs_3064_ = lean_ctor_get(v_x_3059_, 1);
                v_isSharedCheck_3088_ = (!lean_is_exclusive(v_x_3059_)) as u8;
                if v_isSharedCheck_3088_ == 0 {
                    v___x_3066_ = v_x_3059_;
                    v_isShared_3067_ = v_isSharedCheck_3088_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3064_);
                    lean_inc(v_ks_3063_);
                    lean_dec(v_x_3059_);
                    v___x_3066_ = lean_box(0);
                    v_isShared_3067_ = v_isSharedCheck_3088_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3068_ = lean_array_get_size(v_ks_3063_);
                v___x_3069_ = lean_nat_dec_lt(v_x_3060_, v___x_3068_);
                if v___x_3069_ == 0 {
                    lean_dec(v_x_3060_);
                    v___x_3070_ = lean_array_push(v_ks_3063_, v_x_3061_);
                    v___x_3071_ = lean_array_push(v_vs_3064_, v_x_3062_);
                    if v_isShared_3067_ == 0 {
                        lean_ctor_set(v___x_3066_, 1, v___x_3071_);
                        lean_ctor_set(v___x_3066_, 0, v___x_3070_);
                        v___x_3073_ = v___x_3066_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3070_);
                        lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___x_3071_);
                        v___x_3073_ = v_reuseFailAlloc_3074_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3075_ = lean_array_fget_borrowed(v_ks_3063_, v_x_3060_);
                    v___x_3076_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3061_, v_k_x27_3075_);
                    if v___x_3076_ == 0 {
                        if v_isShared_3067_ == 0 {
                            v___x_3078_ = v___x_3066_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_ks_3063_);
                            lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_vs_3064_);
                            v___x_3078_ = v_reuseFailAlloc_3082_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3083_ = lean_array_fset(v_ks_3063_, v_x_3060_, v_x_3061_);
                        v___x_3084_ = lean_array_fset(v_vs_3064_, v_x_3060_, v_x_3062_);
                        lean_dec(v_x_3060_);
                        if v_isShared_3067_ == 0 {
                            lean_ctor_set(v___x_3066_, 1, v___x_3084_);
                            lean_ctor_set(v___x_3066_, 0, v___x_3083_);
                            v___x_3086_ = v___x_3066_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3083_);
                            lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3084_);
                            v___x_3086_ = v_reuseFailAlloc_3087_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3073_;
            }
            3 => {
                v___x_3079_ = lean_unsigned_to_nat(1);
                v___x_3080_ = lean_nat_add(v_x_3060_, v___x_3079_);
                lean_dec(v_x_3060_);
                v_x_3059_ = v___x_3078_;
                v_x_3060_ = v___x_3080_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_n_3089_: *mut LeanObject,
    mut v_k_3090_: *mut LeanObject,
    mut v_v_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_3092_ = lean_unsigned_to_nat(0);
    v___x_3093_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_3089_, v___x_3092_, v_k_3090_, v_v_3091_);
    return v___x_3093_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3094_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3094_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_3095_: *mut LeanObject,
    mut v_x_3096_: usize,
    mut v_x_3097_: usize,
    mut v_x_3098_: *mut LeanObject,
    mut v_x_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: usize = 0;
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v_j_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v_v_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut v_node_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_unused_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: u8 = 0;
    let mut v_ks_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v_reuseFailAlloc_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3095_) == 0 {
                    v_es_3100_ = lean_ctor_get(v_x_3095_, 0);
                    v___x_3101_ = 5usize;
                    v___x_3102_ = 1usize;
                    v___x_3103_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3104_ = lean_usize_land(v_x_3096_, v___x_3103_);
                    v_j_3105_ = lean_usize_to_nat(v___x_3104_);
                    v___x_3106_ = lean_array_get_size(v_es_3100_);
                    v___x_3107_ = lean_nat_dec_lt(v_j_3105_, v___x_3106_);
                    if v___x_3107_ == 0 {
                        lean_dec(v_j_3105_);
                        lean_dec(v_x_3099_);
                        lean_dec(v_x_3098_);
                        return v_x_3095_;
                    } else {
                        lean_inc_ref(v_es_3100_);
                        v_isSharedCheck_3144_ = (!lean_is_exclusive(v_x_3095_)) as u8;
                        if v_isSharedCheck_3144_ == 0 {
                            v_unused_3145_ = lean_ctor_get(v_x_3095_, 0);
                            lean_dec(v_unused_3145_);
                            v___x_3109_ = v_x_3095_;
                            v_isShared_3110_ = v_isSharedCheck_3144_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3095_);
                            v___x_3109_ = lean_box(0);
                            v_isShared_3110_ = v_isSharedCheck_3144_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3146_ = lean_ctor_get(v_x_3095_, 0);
                    v_vs_3147_ = lean_ctor_get(v_x_3095_, 1);
                    v_isSharedCheck_3167_ = (!lean_is_exclusive(v_x_3095_)) as u8;
                    if v_isSharedCheck_3167_ == 0 {
                        v___x_3149_ = v_x_3095_;
                        v_isShared_3150_ = v_isSharedCheck_3167_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3147_);
                        lean_inc(v_ks_3146_);
                        lean_dec(v_x_3095_);
                        v___x_3149_ = lean_box(0);
                        v_isShared_3150_ = v_isSharedCheck_3167_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3111_ = lean_array_fget(v_es_3100_, v_j_3105_);
                v___x_3112_ = lean_box(0);
                v_xs_x27_3113_ = lean_array_fset(v_es_3100_, v_j_3105_, v___x_3112_);
                match lean_obj_tag(v_v_3111_) {
                    0 => {
                        v_key_3120_ = lean_ctor_get(v_v_3111_, 0);
                        v_val_3121_ = lean_ctor_get(v_v_3111_, 1);
                        v_isSharedCheck_3131_ = (!lean_is_exclusive(v_v_3111_)) as u8;
                        if v_isSharedCheck_3131_ == 0 {
                            v___x_3123_ = v_v_3111_;
                            v_isShared_3124_ = v_isSharedCheck_3131_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3121_);
                            lean_inc(v_key_3120_);
                            lean_dec(v_v_3111_);
                            v___x_3123_ = lean_box(0);
                            v_isShared_3124_ = v_isSharedCheck_3131_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3132_ = lean_ctor_get(v_v_3111_, 0);
                        v_isSharedCheck_3142_ = (!lean_is_exclusive(v_v_3111_)) as u8;
                        if v_isSharedCheck_3142_ == 0 {
                            v___x_3134_ = v_v_3111_;
                            v_isShared_3135_ = v_isSharedCheck_3142_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3132_);
                            lean_dec(v_v_3111_);
                            v___x_3134_ = lean_box(0);
                            v_isShared_3135_ = v_isSharedCheck_3142_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3143_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3143_, 0, v_x_3098_);
                        lean_ctor_set(v___x_3143_, 1, v_x_3099_);
                        v___y_3115_ = v___x_3143_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3116_ = lean_array_fset(v_xs_x27_3113_, v_j_3105_, v___y_3115_);
                lean_dec(v_j_3105_);
                if v_isShared_3110_ == 0 {
                    lean_ctor_set(v___x_3109_, 0, v___x_3116_);
                    v___x_3118_ = v___x_3109_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3118_;
            }
            4 => {
                v___x_3125_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3098_, v_key_3120_);
                if v___x_3125_ == 0 {
                    lean_del_object(v___x_3123_);
                    v___x_3126_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3120_,
                        v_val_3121_,
                        v_x_3098_,
                        v_x_3099_,
                    );
                    v___x_3127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3127_, 0, v___x_3126_);
                    v___y_3115_ = v___x_3127_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3121_);
                    lean_dec(v_key_3120_);
                    if v_isShared_3124_ == 0 {
                        lean_ctor_set(v___x_3123_, 1, v_x_3099_);
                        lean_ctor_set(v___x_3123_, 0, v_x_3098_);
                        v___x_3129_ = v___x_3123_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_x_3098_);
                        lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_x_3099_);
                        v___x_3129_ = v_reuseFailAlloc_3130_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3115_ = v___x_3129_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3136_ = lean_usize_shift_right(v_x_3096_, v___x_3101_);
                v___x_3137_ = lean_usize_add(v_x_3097_, v___x_3102_);
                v___x_3138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_node_3132_, v___x_3136_, v___x_3137_, v_x_3098_, v_x_3099_);
                if v_isShared_3135_ == 0 {
                    lean_ctor_set(v___x_3134_, 0, v___x_3138_);
                    v___x_3140_ = v___x_3134_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3115_ = v___x_3140_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3150_ == 0 {
                    v___x_3152_ = v___x_3149_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_ks_3146_);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_vs_3147_);
                    v___x_3152_ = v_reuseFailAlloc_3166_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3153_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(v___x_3152_, v_x_3098_, v_x_3099_);
                v___x_3161_ = 7usize;
                v___x_3162_ = lean_usize_dec_le(v___x_3161_, v_x_3097_);
                if v___x_3162_ == 0 {
                    v___x_3163_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3153_);
                    v___x_3164_ = lean_unsigned_to_nat(4);
                    v___x_3165_ = lean_nat_dec_lt(v___x_3163_, v___x_3164_);
                    lean_dec(v___x_3163_);
                    v___y_3155_ = v___x_3165_;
                    state = 10;
                    continue;
                } else {
                    v___y_3155_ = v___x_3162_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3155_ == 0 {
                    v_ks_3156_ = lean_ctor_get(v_newNode_3153_, 0);
                    lean_inc_ref(v_ks_3156_);
                    v_vs_3157_ = lean_ctor_get(v_newNode_3153_, 1);
                    lean_inc_ref(v_vs_3157_);
                    lean_dec_ref(v_newNode_3153_);
                    v___x_3158_ = lean_unsigned_to_nat(0);
                    v___x_3159_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0);
                    v___x_3160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_x_3097_, v_ks_3156_, v_vs_3157_, v___x_3158_, v___x_3159_);
                    lean_dec_ref(v_vs_3157_);
                    lean_dec_ref(v_ks_3156_);
                    return v___x_3160_;
                } else {
                    return v_newNode_3153_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_depth_3168_: usize,
    mut v_keys_3169_: *mut LeanObject,
    mut v_vals_3170_: *mut LeanObject,
    mut v_i_3171_: *mut LeanObject,
    mut v_entries_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u8 = 0;
    let mut v_k_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u64 = 0;
    let mut v_h_3178_: usize = 0;
    let mut v___x_3179_: usize = 0;
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: usize = 0;
    let mut v___x_3183_: usize = 0;
    let mut v_h_3184_: usize = 0;
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3173_ = lean_array_get_size(v_keys_3169_);
                v___x_3174_ = lean_nat_dec_lt(v_i_3171_, v___x_3173_);
                if v___x_3174_ == 0 {
                    lean_dec(v_i_3171_);
                    return v_entries_3172_;
                } else {
                    v_k_3175_ = lean_array_fget_borrowed(v_keys_3169_, v_i_3171_);
                    v_v_3176_ = lean_array_fget_borrowed(v_vals_3170_, v_i_3171_);
                    v___x_3177_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_3175_);
                    v_h_3178_ = lean_uint64_to_usize(v___x_3177_);
                    v___x_3179_ = 5usize;
                    v___x_3180_ = lean_unsigned_to_nat(1);
                    v___x_3181_ = 1usize;
                    v___x_3182_ = lean_usize_sub(v_depth_3168_, v___x_3181_);
                    v___x_3183_ = lean_usize_mul(v___x_3179_, v___x_3182_);
                    v_h_3184_ = lean_usize_shift_right(v_h_3178_, v___x_3183_);
                    v___x_3185_ = lean_nat_add(v_i_3171_, v___x_3180_);
                    lean_dec(v_i_3171_);
                    lean_inc(v_v_3176_);
                    lean_inc(v_k_3175_);
                    v___x_3186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_entries_3172_, v_h_3184_, v_depth_3168_, v_k_3175_, v_v_3176_);
                    v_i_3171_ = v___x_3185_;
                    v_entries_3172_ = v___x_3186_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_depth_3188_: *mut LeanObject,
    mut v_keys_3189_: *mut LeanObject,
    mut v_vals_3190_: *mut LeanObject,
    mut v_i_3191_: *mut LeanObject,
    mut v_entries_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3193_: usize = 0;
    let mut v_res_3194_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3193_ = lean_unbox_usize(v_depth_3188_);
    lean_dec(v_depth_3188_);
    v_res_3194_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_3193_, v_keys_3189_, v_vals_3190_, v_i_3191_, v_entries_3192_);
    lean_dec_ref(v_vals_3190_);
    lean_dec_ref(v_keys_3189_);
    return v_res_3194_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_3195_: *mut LeanObject,
    mut v_x_3196_: *mut LeanObject,
    mut v_x_3197_: *mut LeanObject,
    mut v_x_3198_: *mut LeanObject,
    mut v_x_3199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1985__boxed_3200_: usize = 0;
    let mut v_x_1986__boxed_3201_: usize = 0;
    let mut v_res_3202_: *mut LeanObject = core::ptr::null_mut();
    v_x_1985__boxed_3200_ = lean_unbox_usize(v_x_3196_);
    lean_dec(v_x_3196_);
    v_x_1986__boxed_3201_ = lean_unbox_usize(v_x_3197_);
    lean_dec(v_x_3197_);
    v_res_3202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_3195_, v_x_1985__boxed_3200_, v_x_1986__boxed_3201_, v_x_3198_, v_x_3199_);
    return v_res_3202_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_3203_: *mut LeanObject,
    mut v_x_3204_: *mut LeanObject,
    mut v_x_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3206_: u64 = 0;
    let mut v___x_3207_: usize = 0;
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    v___x_3206_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_3204_);
    v___x_3207_ = lean_uint64_to_usize(v___x_3206_);
    v___x_3208_ = 1usize;
    v___x_3209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_3203_, v___x_3207_, v___x_3208_, v_x_3204_, v_x_3205_);
    return v___x_3209_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    v___x_3213_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__2;
    v___x_3214_ = lean_unsigned_to_nat(23);
    v___x_3215_ = lean_unsigned_to_nat(166);
    v___x_3216_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__1;
    v___x_3217_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__0;
    v___x_3218_ = l_mkPanicMessageWithDecl(
        v___x_3217_,
        v___x_3216_,
        v___x_3215_,
        v___x_3214_,
        v___x_3213_,
    );
    return v___x_3218_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0(
    mut v_d_3219_: *mut LeanObject,
    mut v_keys_3220_: *mut LeanObject,
    mut v_v_3221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    v___x_3222_ = lean_array_get_size(v_keys_3220_);
    v___x_3223_ = lean_unsigned_to_nat(0);
    v___x_3224_ = lean_nat_dec_eq(v___x_3222_, v___x_3223_);
    if v___x_3224_ == 0 {
        let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
        v___x_3225_ = lean_box(0);
        v_k_3226_ = lean_array_get_borrowed(v___x_3225_, v_keys_3220_, v___x_3223_);
        v___x_3227_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0___redArg(v_d_3219_, v_k_3226_);
        if lean_obj_tag(v___x_3227_) == 0 {
            let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_3229_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
            v___x_3228_ = lean_unsigned_to_nat(1);
            v_c_3229_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                lean_box(0),
                v_keys_3220_,
                v_v_3221_,
                v___x_3228_,
            );
            lean_inc(v_k_3226_);
            v___x_3230_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_3219_, v_k_3226_, v_c_3229_);
            return v___x_3230_;
        } else {
            let mut v_val_3231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_3233_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
            v_val_3231_ = lean_ctor_get(v___x_3227_, 0);
            lean_inc(v_val_3231_);
            lean_dec_ref_known(v___x_3227_, 1);
            v___x_3232_ = lean_unsigned_to_nat(1);
            v_c_3233_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2(v_keys_3220_, v_v_3221_, v___x_3232_, v_val_3231_);
            lean_inc(v_k_3226_);
            v___x_3234_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_3219_, v_k_3226_, v_c_3233_);
            return v___x_3234_;
        }
    } else {
        let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_v_3221_);
        lean_dec_ref(v_d_3219_);
        v___x_3235_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___closed__3);
        v___x_3236_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3(v___x_3235_);
        return v___x_3236_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0___boxed(
    mut v_d_3237_: *mut LeanObject,
    mut v_keys_3238_: *mut LeanObject,
    mut v_v_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3240_: *mut LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0(v_d_3237_, v_keys_3238_, v_v_3239_);
    lean_dec_ref(v_keys_3238_);
    return v_res_3240_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__1_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_(
    mut v_dt_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3243_ = lean_ctor_get(v_x_3242_, 0);
    lean_inc(v_fst_3243_);
    v_snd_3244_ = lean_ctor_get(v_x_3242_, 1);
    lean_inc(v_snd_3244_);
    lean_dec_ref(v_x_3242_);
    v___x_3245_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0(v_dt_3241_, v_snd_3244_, v_fst_3243_);
    lean_dec(v_snd_3244_);
    return v___x_3245_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_(
    mut v___y_3246_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3246_);
    return v___y_3246_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2____boxed(
    mut v___y_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3248_: *mut LeanObject = core::ptr::null_mut();
    v_res_3248_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_(v___y_3247_);
    lean_dec_ref(v___y_3247_);
    return v_res_3248_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    v___x_3261_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3261_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    v___x_3262_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_);
    v___x_3263_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3263_, 0, v___x_3262_);
    return v___x_3263_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    v___f_3264_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_;
    v___f_3265_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_;
    v___x_3266_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_);
    v___f_3267_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_;
    v___x_3268_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_;
    v___x_3269_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3269_, 0, v___x_3268_);
    lean_ctor_set(v___x_3269_, 1, v___f_3267_);
    lean_ctor_set(v___x_3269_, 2, v___x_3266_);
    lean_ctor_set(v___x_3269_, 3, v___f_3265_);
    lean_ctor_set(v___x_3269_, 4, v___f_3264_);
    return v___x_3269_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    v___x_3271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_);
    v___x_3272_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3271_);
    return v___x_3272_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2____boxed(
    mut v_a_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3274_: *mut LeanObject = core::ptr::null_mut();
    v_res_3274_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_();
    return v_res_3274_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_3275_: *mut LeanObject,
    mut v_x_3276_: *mut LeanObject,
    mut v_x_3277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    v___x_3278_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_3276_, v_x_3277_);
    return v___x_3278_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_3279_: *mut LeanObject,
    mut v_x_3280_: *mut LeanObject,
    mut v_x_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3282_: *mut LeanObject = core::ptr::null_mut();
    v_res_3282_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_3279_, v_x_3280_, v_x_3281_);
    lean_dec(v_x_3281_);
    lean_dec_ref(v_x_3280_);
    return v_res_3282_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_3283_: *mut LeanObject,
    mut v_x_3284_: *mut LeanObject,
    mut v_x_3285_: *mut LeanObject,
    mut v_x_3286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    v___x_3287_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_3284_, v_x_3285_, v_x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_3288_: *mut LeanObject,
    mut v_x_3289_: *mut LeanObject,
    mut v_x_3290_: usize,
    mut v_x_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    v___x_3292_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_3289_, v_x_3290_, v_x_3291_);
    return v___x_3292_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3293_: *mut LeanObject,
    mut v_x_3294_: *mut LeanObject,
    mut v_x_3295_: *mut LeanObject,
    mut v_x_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2303__boxed_3297_: usize = 0;
    let mut v_res_3298_: *mut LeanObject = core::ptr::null_mut();
    v_x_2303__boxed_3297_ = lean_unbox_usize(v_x_3295_);
    lean_dec(v_x_3295_);
    v_res_3298_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_3293_, v_x_3294_, v_x_2303__boxed_3297_, v_x_3296_);
    lean_dec(v_x_3296_);
    lean_dec_ref(v_x_3294_);
    return v_res_3298_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_3299_: *mut LeanObject,
    mut v_x_3300_: *mut LeanObject,
    mut v_x_3301_: usize,
    mut v_x_3302_: usize,
    mut v_x_3303_: *mut LeanObject,
    mut v_x_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    v___x_3305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_3300_, v_x_3301_, v_x_3302_, v_x_3303_, v_x_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3306_: *mut LeanObject,
    mut v_x_3307_: *mut LeanObject,
    mut v_x_3308_: *mut LeanObject,
    mut v_x_3309_: *mut LeanObject,
    mut v_x_3310_: *mut LeanObject,
    mut v_x_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2314__boxed_3312_: usize = 0;
    let mut v_x_2315__boxed_3313_: usize = 0;
    let mut v_res_3314_: *mut LeanObject = core::ptr::null_mut();
    v_x_2314__boxed_3312_ = lean_unbox_usize(v_x_3308_);
    lean_dec(v_x_3308_);
    v_x_2315__boxed_3313_ = lean_unbox_usize(v_x_3309_);
    lean_dec(v_x_3309_);
    v_res_3314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_3306_, v_x_3307_, v_x_2314__boxed_3312_, v_x_2315__boxed_3313_, v_x_3310_, v_x_3311_);
    return v_res_3314_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3315_: *mut LeanObject,
    mut v_keys_3316_: *mut LeanObject,
    mut v_vals_3317_: *mut LeanObject,
    mut v_heq_3318_: *mut LeanObject,
    mut v_i_3319_: *mut LeanObject,
    mut v_k_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    v___x_3321_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3316_, v_vals_3317_, v_i_3319_, v_k_3320_);
    return v___x_3321_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3322_: *mut LeanObject,
    mut v_keys_3323_: *mut LeanObject,
    mut v_vals_3324_: *mut LeanObject,
    mut v_heq_3325_: *mut LeanObject,
    mut v_i_3326_: *mut LeanObject,
    mut v_k_3327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3328_: *mut LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3322_, v_keys_3323_, v_vals_3324_, v_heq_3325_, v_i_3326_, v_k_3327_);
    lean_dec(v_k_3327_);
    lean_dec_ref(v_vals_3324_);
    lean_dec_ref(v_keys_3323_);
    return v_res_3328_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_3329_: *mut LeanObject,
    mut v_n_3330_: *mut LeanObject,
    mut v_k_3331_: *mut LeanObject,
    mut v_v_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    v___x_3333_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6___redArg(v_n_3330_, v_k_3331_, v_v_3332_);
    return v___x_3333_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_3334_: *mut LeanObject,
    mut v_depth_3335_: usize,
    mut v_keys_3336_: *mut LeanObject,
    mut v_vals_3337_: *mut LeanObject,
    mut v_heq_3338_: *mut LeanObject,
    mut v_i_3339_: *mut LeanObject,
    mut v_entries_3340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    v___x_3341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_depth_3335_, v_keys_3336_, v_vals_3337_, v_i_3339_, v_entries_3340_);
    return v___x_3341_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_3342_: *mut LeanObject,
    mut v_depth_3343_: *mut LeanObject,
    mut v_keys_3344_: *mut LeanObject,
    mut v_vals_3345_: *mut LeanObject,
    mut v_heq_3346_: *mut LeanObject,
    mut v_i_3347_: *mut LeanObject,
    mut v_entries_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3349_: usize = 0;
    let mut v_res_3350_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3349_ = lean_unbox_usize(v_depth_3343_);
    lean_dec(v_depth_3343_);
    v_res_3350_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_3342_, v_depth_boxed_3349_, v_keys_3344_, v_vals_3345_, v_heq_3346_, v_i_3347_, v_entries_3348_);
    lean_dec_ref(v_vals_3345_);
    lean_dec_ref(v_keys_3344_);
    return v_res_3350_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(
    mut v_x_3351_: *mut LeanObject,
    mut v_keys_3352_: *mut LeanObject,
    mut v_v_3353_: *mut LeanObject,
    mut v_k_3354_: *mut LeanObject,
    mut v_as_3355_: *mut LeanObject,
    mut v_k_3356_: *mut LeanObject,
    mut v_x_3357_: *mut LeanObject,
    mut v_x_3358_: *mut LeanObject,
    mut v_x_3359_: *mut LeanObject,
    mut v_x_3360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    v___x_3361_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___redArg(v_x_3351_, v_keys_3352_, v_v_3353_, v_k_3354_, v_as_3355_, v_k_3356_, v_x_3357_, v_x_3358_);
    return v___x_3361_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_x_3362_: *mut LeanObject,
    mut v_keys_3363_: *mut LeanObject,
    mut v_v_3364_: *mut LeanObject,
    mut v_k_3365_: *mut LeanObject,
    mut v_as_3366_: *mut LeanObject,
    mut v_k_3367_: *mut LeanObject,
    mut v_x_3368_: *mut LeanObject,
    mut v_x_3369_: *mut LeanObject,
    mut v_x_3370_: *mut LeanObject,
    mut v_x_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3372_: *mut LeanObject = core::ptr::null_mut();
    v_res_3372_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__12(v_x_3362_, v_keys_3363_, v_v_3364_, v_k_3365_, v_as_3366_, v_k_3367_, v_x_3368_, v_x_3369_, v_x_3370_, v_x_3371_);
    lean_dec_ref(v_k_3367_);
    lean_dec_ref(v_keys_3363_);
    lean_dec(v_x_3362_);
    return v_res_3372_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_3373_: *mut LeanObject,
    mut v_x_3374_: *mut LeanObject,
    mut v_x_3375_: *mut LeanObject,
    mut v_x_3376_: *mut LeanObject,
    mut v_x_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3378_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_3374_, v_x_3375_, v_x_3376_, v_x_3377_);
    return v___x_3378_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3379_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    v___x_3380_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__0);
    v___x_3381_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3381_, 0, v___x_3380_);
    return v___x_3381_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    v___x_3382_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1);
    v___x_3383_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3383_, 0, v___x_3382_);
    lean_ctor_set(v___x_3383_, 1, v___x_3382_);
    return v___x_3383_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    v___x_3384_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__1);
    v___x_3385_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3385_, 0, v___x_3384_);
    lean_ctor_set(v___x_3385_, 1, v___x_3384_);
    lean_ctor_set(v___x_3385_, 2, v___x_3384_);
    lean_ctor_set(v___x_3385_, 3, v___x_3384_);
    lean_ctor_set(v___x_3385_, 4, v___x_3384_);
    lean_ctor_set(v___x_3385_, 5, v___x_3384_);
    return v___x_3385_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg(
    mut v_ext_3386_: *mut LeanObject,
    mut v_b_3387_: *mut LeanObject,
    mut v_kind_3388_: u8,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3405_: u8 = 0;
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3426_: u8 = 0;
    let mut v_unused_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3429_: u8 = 0;
    let mut v_unused_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_3393_ = lean_ctor_get(v___y_3390_, 6);
                v___x_3394_ = lean_st_ref_take(v___y_3391_);
                v_env_3395_ = lean_ctor_get(v___x_3394_, 0);
                v_nextMacroScope_3396_ = lean_ctor_get(v___x_3394_, 1);
                v_ngen_3397_ = lean_ctor_get(v___x_3394_, 2);
                v_auxDeclNGen_3398_ = lean_ctor_get(v___x_3394_, 3);
                v_traceState_3399_ = lean_ctor_get(v___x_3394_, 4);
                v_messages_3400_ = lean_ctor_get(v___x_3394_, 6);
                v_infoState_3401_ = lean_ctor_get(v___x_3394_, 7);
                v_snapshotTasks_3402_ = lean_ctor_get(v___x_3394_, 8);
                v_isSharedCheck_3429_ = (!lean_is_exclusive(v___x_3394_)) as u8;
                if v_isSharedCheck_3429_ == 0 {
                    v_unused_3430_ = lean_ctor_get(v___x_3394_, 5);
                    lean_dec(v_unused_3430_);
                    v___x_3404_ = v___x_3394_;
                    v_isShared_3405_ = v_isSharedCheck_3429_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3402_);
                    lean_inc(v_infoState_3401_);
                    lean_inc(v_messages_3400_);
                    lean_inc(v_traceState_3399_);
                    lean_inc(v_auxDeclNGen_3398_);
                    lean_inc(v_ngen_3397_);
                    lean_inc(v_nextMacroScope_3396_);
                    lean_inc(v_env_3395_);
                    lean_dec(v___x_3394_);
                    v___x_3404_ = lean_box(0);
                    v_isShared_3405_ = v_isSharedCheck_3429_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_3393_);
                v___x_3406_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_3395_,
                    v_ext_3386_,
                    v_b_3387_,
                    v_kind_3388_,
                    v_currNamespace_3393_,
                );
                v___x_3407_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__2);
                if v_isShared_3405_ == 0 {
                    lean_ctor_set(v___x_3404_, 5, v___x_3407_);
                    lean_ctor_set(v___x_3404_, 0, v___x_3406_);
                    v___x_3409_ = v___x_3404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3406_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_nextMacroScope_3396_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_ngen_3397_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_auxDeclNGen_3398_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 4, v_traceState_3399_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 5, v___x_3407_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 6, v_messages_3400_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 7, v_infoState_3401_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 8, v_snapshotTasks_3402_);
                    v___x_3409_ = v_reuseFailAlloc_3428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3410_ = lean_st_ref_set(v___y_3391_, v___x_3409_);
                v___x_3411_ = lean_st_ref_take(v___y_3389_);
                v_mctx_3412_ = lean_ctor_get(v___x_3411_, 0);
                v_zetaDeltaFVarIds_3413_ = lean_ctor_get(v___x_3411_, 2);
                v_postponed_3414_ = lean_ctor_get(v___x_3411_, 3);
                v_diag_3415_ = lean_ctor_get(v___x_3411_, 4);
                v_isSharedCheck_3426_ = (!lean_is_exclusive(v___x_3411_)) as u8;
                if v_isSharedCheck_3426_ == 0 {
                    v_unused_3427_ = lean_ctor_get(v___x_3411_, 1);
                    lean_dec(v_unused_3427_);
                    v___x_3417_ = v___x_3411_;
                    v_isShared_3418_ = v_isSharedCheck_3426_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_3415_);
                    lean_inc(v_postponed_3414_);
                    lean_inc(v_zetaDeltaFVarIds_3413_);
                    lean_inc(v_mctx_3412_);
                    lean_dec(v___x_3411_);
                    v___x_3417_ = lean_box(0);
                    v_isShared_3418_ = v_isSharedCheck_3426_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3419_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___closed__3);
                if v_isShared_3418_ == 0 {
                    lean_ctor_set(v___x_3417_, 1, v___x_3419_);
                    v___x_3421_ = v___x_3417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_mctx_3412_);
                    lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3419_);
                    lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_zetaDeltaFVarIds_3413_);
                    lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_postponed_3414_);
                    lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_diag_3415_);
                    v___x_3421_ = v_reuseFailAlloc_3425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3422_ = lean_st_ref_set(v___y_3389_, v___x_3421_);
                v___x_3423_ = lean_box(0);
                v___x_3424_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3424_, 0, v___x_3423_);
                return v___x_3424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_ext_3431_: *mut LeanObject,
    mut v_b_3432_: *mut LeanObject,
    mut v_kind_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3438_: u8 = 0;
    let mut v_res_3439_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3438_ = (lean_unbox(v_kind_3433_) as u8);
    v_res_3439_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg(v_ext_3431_, v_b_3432_, v_kind_boxed_3438_, v___y_3434_, v___y_3435_, v___y_3436_);
    lean_dec(v___y_3436_);
    lean_dec_ref(v___y_3435_);
    lean_dec(v___y_3434_);
    return v_res_3439_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_3440_: *mut LeanObject,
    mut v_00_u03b2_3441_: *mut LeanObject,
    mut v_00_u03c3_3442_: *mut LeanObject,
    mut v_ext_3443_: *mut LeanObject,
    mut v_b_3444_: *mut LeanObject,
    mut v_kind_3445_: u8,
    mut v___y_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    v___x_3451_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg(v_ext_3443_, v_b_3444_, v_kind_3445_, v___y_3447_, v___y_3448_, v___y_3449_);
    return v___x_3451_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_3452_: *mut LeanObject,
    mut v_00_u03b2_3453_: *mut LeanObject,
    mut v_00_u03c3_3454_: *mut LeanObject,
    mut v_ext_3455_: *mut LeanObject,
    mut v_b_3456_: *mut LeanObject,
    mut v_kind_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3463_: u8 = 0;
    let mut v_res_3464_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3463_ = (lean_unbox(v_kind_3457_) as u8);
    v_res_3464_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1(v_00_u03b1_3452_, v_00_u03b2_3453_, v_00_u03c3_3454_, v_ext_3455_, v_b_3456_, v_kind_boxed_3463_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
    lean_dec(v___y_3461_);
    lean_dec_ref(v___y_3460_);
    lean_dec(v___y_3459_);
    lean_dec_ref(v___y_3458_);
    return v_res_3464_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2___redArg(
    mut v_k_3465_: *mut LeanObject,
    mut v_allowLevelAssignments_3466_: u8,
    mut v___y_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v_a_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_3466_,
                    v_k_3465_,
                    v___y_3467_,
                    v___y_3468_,
                    v___y_3469_,
                    v___y_3470_,
                );
                if lean_obj_tag(v___x_3472_) == 0 {
                    v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
                    v_isSharedCheck_3480_ = (!lean_is_exclusive(v___x_3472_)) as u8;
                    if v_isSharedCheck_3480_ == 0 {
                        v___x_3475_ = v___x_3472_;
                        v_isShared_3476_ = v_isSharedCheck_3480_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3473_);
                        lean_dec(v___x_3472_);
                        v___x_3475_ = lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3480_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3481_ = lean_ctor_get(v___x_3472_, 0);
                    v_isSharedCheck_3488_ = (!lean_is_exclusive(v___x_3472_)) as u8;
                    if v_isSharedCheck_3488_ == 0 {
                        v___x_3483_ = v___x_3472_;
                        v_isShared_3484_ = v_isSharedCheck_3488_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3481_);
                        lean_dec(v___x_3472_);
                        v___x_3483_ = lean_box(0);
                        v_isShared_3484_ = v_isSharedCheck_3488_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3476_ == 0 {
                    v___x_3478_ = v___x_3475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
                    v___x_3478_ = v_reuseFailAlloc_3479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3478_;
            }
            3 => {
                if v_isShared_3484_ == 0 {
                    v___x_3486_ = v___x_3483_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
                    v___x_3486_ = v_reuseFailAlloc_3487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_k_3489_: *mut LeanObject,
    mut v_allowLevelAssignments_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3496_: u8 = 0;
    let mut v_res_3497_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3496_ = (lean_unbox(v_allowLevelAssignments_3490_) as u8);
    v_res_3497_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2___redArg(v_k_3489_, v_allowLevelAssignments_boxed_3496_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
    lean_dec(v___y_3494_);
    lean_dec_ref(v___y_3493_);
    lean_dec(v___y_3492_);
    lean_dec_ref(v___y_3491_);
    return v_res_3497_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2(
    mut v_00_u03b1_3498_: *mut LeanObject,
    mut v_k_3499_: *mut LeanObject,
    mut v_allowLevelAssignments_3500_: u8,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3506_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2___redArg(v_k_3499_, v_allowLevelAssignments_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
    return v___x_3506_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b1_3507_: *mut LeanObject,
    mut v_k_3508_: *mut LeanObject,
    mut v_allowLevelAssignments_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3515_: u8 = 0;
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3515_ = (lean_unbox(v_allowLevelAssignments_3509_) as u8);
    v_res_3516_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2(v_00_u03b1_3507_, v_k_3508_, v_allowLevelAssignments_boxed_3515_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
    lean_dec(v___y_3513_);
    lean_dec_ref(v___y_3512_);
    lean_dec(v___y_3511_);
    lean_dec_ref(v___y_3510_);
    return v_res_3516_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(
    mut v_arg_3517_: *mut LeanObject,
    mut v_arg_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    v___x_3524_ = l_Lean_Meta_isExprDefEq(
        v_arg_3517_,
        v_arg_3518_,
        v___y_3519_,
        v___y_3520_,
        v___y_3521_,
        v___y_3522_,
    );
    return v___x_3524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v_arg_3525_: *mut LeanObject,
    mut v_arg_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
    mut v___y_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3532_: *mut LeanObject = core::ptr::null_mut();
    v_res_3532_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v_arg_3525_, v_arg_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
    lean_dec(v___y_3530_);
    lean_dec_ref(v___y_3529_);
    lean_dec(v___y_3528_);
    lean_dec_ref(v___y_3527_);
    return v_res_3532_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3_spec__4(
    mut v_msgData_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    v___x_3539_ = lean_st_ref_get(v___y_3537_);
    v_env_3540_ = lean_ctor_get(v___x_3539_, 0);
    lean_inc_ref(v_env_3540_);
    lean_dec(v___x_3539_);
    v___x_3541_ = lean_st_ref_get(v___y_3535_);
    v_mctx_3542_ = lean_ctor_get(v___x_3541_, 0);
    lean_inc_ref(v_mctx_3542_);
    lean_dec(v___x_3541_);
    v_lctx_3543_ = lean_ctor_get(v___y_3534_, 2);
    v_options_3544_ = lean_ctor_get(v___y_3536_, 2);
    lean_inc_ref(v_options_3544_);
    lean_inc_ref(v_lctx_3543_);
    v___x_3545_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3545_, 0, v_env_3540_);
    lean_ctor_set(v___x_3545_, 1, v_mctx_3542_);
    lean_ctor_set(v___x_3545_, 2, v_lctx_3543_);
    lean_ctor_set(v___x_3545_, 3, v_options_3544_);
    v___x_3546_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3546_, 0, v___x_3545_);
    lean_ctor_set(v___x_3546_, 1, v_msgData_3533_);
    v___x_3547_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3547_, 0, v___x_3546_);
    return v___x_3547_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3_spec__4___boxed(
    mut v_msgData_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3554_: *mut LeanObject = core::ptr::null_mut();
    v_res_3554_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3_spec__4(v_msgData_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
    lean_dec(v___y_3552_);
    lean_dec_ref(v___y_3551_);
    lean_dec(v___y_3550_);
    lean_dec_ref(v___y_3549_);
    return v_res_3554_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(
    mut v_msg_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3561_ = lean_ctor_get(v___y_3558_, 5);
                v___x_3562_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3_spec__4(v_msg_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
                v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
                v_isSharedCheck_3571_ = (!lean_is_exclusive(v___x_3562_)) as u8;
                if v_isSharedCheck_3571_ == 0 {
                    v___x_3565_ = v___x_3562_;
                    v_isShared_3566_ = v_isSharedCheck_3571_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3563_);
                    lean_dec(v___x_3562_);
                    v___x_3565_ = lean_box(0);
                    v_isShared_3566_ = v_isSharedCheck_3571_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3561_);
                v___x_3567_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3567_, 0, v_ref_3561_);
                lean_ctor_set(v___x_3567_, 1, v_a_3563_);
                if v_isShared_3566_ == 0 {
                    lean_ctor_set_tag(v___x_3565_, 1);
                    lean_ctor_set(v___x_3565_, 0, v___x_3567_);
                    v___x_3569_ = v___x_3565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
                    v___x_3569_ = v_reuseFailAlloc_3570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg___boxed(
    mut v_msg_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
    mut v___y_3575_: *mut LeanObject,
    mut v___y_3576_: *mut LeanObject,
    mut v___y_3577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3578_: *mut LeanObject = core::ptr::null_mut();
    v_res_3578_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v_msg_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
    lean_dec(v___y_3576_);
    lean_dec_ref(v___y_3575_);
    lean_dec(v___y_3574_);
    lean_dec_ref(v___y_3573_);
    return v_res_3578_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(
    mut v___f_3579_: *mut LeanObject,
    mut v___x_3580_: u8,
    mut v_fn_3581_: *mut LeanObject,
    mut v_decl_3582_: *mut LeanObject,
    mut v_kind_3583_: u8,
    mut v___x_3584_: *mut LeanObject,
    mut v_____r_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
    mut v___y_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
    mut v___y_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3609_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__2___redArg(v___f_3579_, v___x_3580_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
                if lean_obj_tag(v___x_3609_) == 0 {
                    v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
                    lean_inc(v_a_3610_);
                    lean_dec_ref_known(v___x_3609_, 1);
                    v___x_3611_ = (lean_unbox(v_a_3610_) as u8);
                    lean_dec(v_a_3610_);
                    if v___x_3611_ == 0 {
                        lean_dec(v_decl_3582_);
                        lean_dec_ref(v_fn_3581_);
                        v___x_3612_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_3584_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
                        return v___x_3612_;
                    } else {
                        lean_dec_ref(v___x_3584_);
                        v___y_3592_ = v___y_3586_;
                        v___y_3593_ = v___y_3587_;
                        v___y_3594_ = v___y_3588_;
                        v___y_3595_ = v___y_3589_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3584_);
                    lean_dec(v_decl_3582_);
                    lean_dec_ref(v_fn_3581_);
                    v_a_3613_ = lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3620_ = (!lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3620_ == 0 {
                        v___x_3615_ = v___x_3609_;
                        v_isShared_3616_ = v_isSharedCheck_3620_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3613_);
                        lean_dec(v___x_3609_);
                        v___x_3615_ = lean_box(0);
                        v_isShared_3616_ = v_isSharedCheck_3620_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3596_ = l_Lean_Meta_DiscrTree_mkPath(
                    v_fn_3581_,
                    v___x_3580_,
                    v___y_3592_,
                    v___y_3593_,
                    v___y_3594_,
                    v___y_3595_,
                );
                if lean_obj_tag(v___x_3596_) == 0 {
                    v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
                    lean_inc(v_a_3597_);
                    lean_dec_ref_known(v___x_3596_, 1);
                    v___x_3598_ = l_Lean_Meta_Rfl_reflExt;
                    v___x_3599_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3599_, 0, v_decl_3582_);
                    lean_ctor_set(v___x_3599_, 1, v_a_3597_);
                    v___x_3600_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__1___redArg(v___x_3598_, v___x_3599_, v_kind_3583_, v___y_3593_, v___y_3594_, v___y_3595_);
                    return v___x_3600_;
                } else {
                    lean_dec(v_decl_3582_);
                    v_a_3601_ = lean_ctor_get(v___x_3596_, 0);
                    v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3596_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3603_ = v___x_3596_;
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3601_);
                        lean_dec(v___x_3596_);
                        v___x_3603_ = lean_box(0);
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3604_ == 0 {
                    v___x_3606_ = v___x_3603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3606_;
            }
            4 => {
                if v_isShared_3616_ == 0 {
                    v___x_3618_ = v___x_3615_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
                    v___x_3618_ = v_reuseFailAlloc_3619_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v___f_3621_: *mut LeanObject,
    mut v___x_3622_: *mut LeanObject,
    mut v_fn_3623_: *mut LeanObject,
    mut v_decl_3624_: *mut LeanObject,
    mut v_kind_3625_: *mut LeanObject,
    mut v___x_3626_: *mut LeanObject,
    mut v_____r_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7449__boxed_3633_: u8 = 0;
    let mut v_kind_boxed_3634_: u8 = 0;
    let mut v_res_3635_: *mut LeanObject = core::ptr::null_mut();
    v___x_7449__boxed_3633_ = (lean_unbox(v___x_3622_) as u8);
    v_kind_boxed_3634_ = (lean_unbox(v_kind_3625_) as u8);
    v_res_3635_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_3621_, v___x_7449__boxed_3633_, v_fn_3623_, v_decl_3624_, v_kind_boxed_3634_, v___x_3626_, v_____r_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
    lean_dec(v___y_3631_);
    lean_dec_ref(v___y_3630_);
    lean_dec(v___y_3629_);
    lean_dec_ref(v___y_3628_);
    return v_res_3635_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(
    mut v___f_3636_: *mut LeanObject,
    mut v_x_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
    mut v___y_3641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    v___x_3643_ = lean_box(0);
    lean_inc(v___y_3641_);
    lean_inc_ref(v___y_3640_);
    lean_inc(v___y_3639_);
    lean_inc_ref(v___y_3638_);
    v___x_3644_ = lean_apply_6(
        v___f_3636_,
        v___x_3643_,
        v___y_3638_,
        v___y_3639_,
        v___y_3640_,
        v___y_3641_,
        lean_box(0),
    );
    return v___x_3644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v___f_3645_: *mut LeanObject,
    mut v_x_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_res_3652_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_3645_, v_x_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
    lean_dec(v___y_3650_);
    lean_dec_ref(v___y_3649_);
    lean_dec(v___y_3648_);
    lean_dec_ref(v___y_3647_);
    lean_dec_ref(v_x_3646_);
    return v_res_3652_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    v___x_3653_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3653_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    v___x_3654_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__0);
    v___x_3655_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3655_, 0, v___x_3654_);
    return v___x_3655_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1);
    v___x_3657_ = lean_unsigned_to_nat(0);
    v___x_3658_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3658_, 0, v___x_3657_);
    lean_ctor_set(v___x_3658_, 1, v___x_3657_);
    lean_ctor_set(v___x_3658_, 2, v___x_3657_);
    lean_ctor_set(v___x_3658_, 3, v___x_3657_);
    lean_ctor_set(v___x_3658_, 4, v___x_3656_);
    lean_ctor_set(v___x_3658_, 5, v___x_3656_);
    lean_ctor_set(v___x_3658_, 6, v___x_3656_);
    lean_ctor_set(v___x_3658_, 7, v___x_3656_);
    lean_ctor_set(v___x_3658_, 8, v___x_3656_);
    lean_ctor_set(v___x_3658_, 9, v___x_3656_);
    return v___x_3658_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v___x_3659_ = lean_unsigned_to_nat(32);
    v___x_3660_ = lean_mk_empty_array_with_capacity(v___x_3659_);
    v___x_3661_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3661_, 0, v___x_3660_);
    return v___x_3661_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3662_: usize = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    v___x_3662_ = 5usize;
    v___x_3663_ = lean_unsigned_to_nat(0);
    v___x_3664_ = lean_unsigned_to_nat(32);
    v___x_3665_ = lean_mk_empty_array_with_capacity(v___x_3664_);
    v___x_3666_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3);
    v___x_3667_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    lean_ctor_set(v___x_3667_, 1, v___x_3665_);
    lean_ctor_set(v___x_3667_, 2, v___x_3663_);
    lean_ctor_set(v___x_3667_, 3, v___x_3663_);
    lean_ctor_set_usize(v___x_3667_, 4, v___x_3662_);
    return v___x_3667_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    v___x_3668_ = lean_box(1);
    v___x_3669_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__4);
    v___x_3670_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__1);
    v___x_3671_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3671_, 0, v___x_3670_);
    lean_ctor_set(v___x_3671_, 1, v___x_3669_);
    lean_ctor_set(v___x_3671_, 2, v___x_3668_);
    return v___x_3671_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    v___x_3673_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__6;
    v___x_3674_ = l_Lean_stringToMessageData(v___x_3673_);
    return v___x_3674_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3676_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__8;
    v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    v___x_3679_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__10;
    v___x_3680_ = l_Lean_stringToMessageData(v___x_3679_);
    return v___x_3680_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    v___x_3682_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__12;
    v___x_3683_ = l_Lean_stringToMessageData(v___x_3682_);
    return v___x_3683_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    v___x_3685_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__14;
    v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
    return v___x_3686_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    v___x_3688_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__16;
    v___x_3689_ = l_Lean_stringToMessageData(v___x_3688_);
    return v___x_3689_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v___x_3691_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__18;
    v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
    return v___x_3692_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg(
    mut v_msg_3693_: *mut LeanObject,
    mut v_declHint_3694_: *mut LeanObject,
    mut v___y_3695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: u8 = 0;
    let mut v_isExporting_3700_: u8 = 0;
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3722_: u8 = 0;
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: u8 = 0;
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3697_ = lean_st_ref_get(v___y_3695_);
                v_env_3698_ = lean_ctor_get(v___x_3697_, 0);
                lean_inc_ref(v_env_3698_);
                lean_dec(v___x_3697_);
                v___x_3699_ = l_Lean_Name_isAnonymous(v_declHint_3694_);
                if v___x_3699_ == 0 {
                    v_isExporting_3700_ = lean_ctor_get_uint8(
                        v_env_3698_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3700_ == 0 {
                        lean_dec_ref(v_env_3698_);
                        lean_dec(v_declHint_3694_);
                        v___x_3701_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3701_, 0, v_msg_3693_);
                        return v___x_3701_;
                    } else {
                        lean_inc_ref(v_env_3698_);
                        v___x_3702_ = l_Lean_Environment_setExporting(v_env_3698_, v___x_3699_);
                        lean_inc(v_declHint_3694_);
                        lean_inc_ref(v___x_3702_);
                        v___x_3703_ = l_Lean_Environment_contains(
                            v___x_3702_,
                            v_declHint_3694_,
                            v_isExporting_3700_,
                        );
                        if v___x_3703_ == 0 {
                            lean_dec_ref(v___x_3702_);
                            lean_dec_ref(v_env_3698_);
                            lean_dec(v_declHint_3694_);
                            v___x_3704_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3704_, 0, v_msg_3693_);
                            return v___x_3704_;
                        } else {
                            v___x_3705_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2);
                            v___x_3706_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5);
                            v___x_3707_ = l_Lean_Options_empty;
                            v___x_3708_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3708_, 0, v___x_3702_);
                            lean_ctor_set(v___x_3708_, 1, v___x_3705_);
                            lean_ctor_set(v___x_3708_, 2, v___x_3706_);
                            lean_ctor_set(v___x_3708_, 3, v___x_3707_);
                            lean_inc(v_declHint_3694_);
                            v___x_3709_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3694_, v___x_3699_);
                            v_c_3710_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3710_, 0, v___x_3708_);
                            lean_ctor_set(v_c_3710_, 1, v___x_3709_);
                            v___x_3711_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3698_,
                                v_declHint_3694_,
                            );
                            if lean_obj_tag(v___x_3711_) == 0 {
                                lean_dec_ref(v_env_3698_);
                                lean_dec(v_declHint_3694_);
                                v___x_3712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7);
                                v___x_3713_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3713_, 0, v___x_3712_);
                                lean_ctor_set(v___x_3713_, 1, v_c_3710_);
                                v___x_3714_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__9);
                                v___x_3715_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3715_, 0, v___x_3713_);
                                lean_ctor_set(v___x_3715_, 1, v___x_3714_);
                                v___x_3716_ = l_Lean_MessageData_note(v___x_3715_);
                                v___x_3717_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3717_, 0, v_msg_3693_);
                                lean_ctor_set(v___x_3717_, 1, v___x_3716_);
                                v___x_3718_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3718_, 0, v___x_3717_);
                                return v___x_3718_;
                            } else {
                                v_val_3719_ = lean_ctor_get(v___x_3711_, 0);
                                v_isSharedCheck_3754_ = (!lean_is_exclusive(v___x_3711_)) as u8;
                                if v_isSharedCheck_3754_ == 0 {
                                    v___x_3721_ = v___x_3711_;
                                    v_isShared_3722_ = v_isSharedCheck_3754_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3719_);
                                    lean_dec(v___x_3711_);
                                    v___x_3721_ = lean_box(0);
                                    v_isShared_3722_ = v_isSharedCheck_3754_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3698_);
                    lean_dec(v_declHint_3694_);
                    v___x_3755_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3755_, 0, v_msg_3693_);
                    return v___x_3755_;
                }
            }
            1 => {
                v___x_3723_ = lean_box(0);
                v___x_3724_ = l_Lean_Environment_header(v_env_3698_);
                lean_dec_ref(v_env_3698_);
                v___x_3725_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3724_);
                v_mod_3726_ = lean_array_get(v___x_3723_, v___x_3725_, v_val_3719_);
                lean_dec(v_val_3719_);
                lean_dec_ref(v___x_3725_);
                v___x_3727_ = l_Lean_isPrivateName(v_declHint_3694_);
                lean_dec(v_declHint_3694_);
                if v___x_3727_ == 0 {
                    v___x_3728_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__11);
                    v___x_3729_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3729_, 0, v___x_3728_);
                    lean_ctor_set(v___x_3729_, 1, v_c_3710_);
                    v___x_3730_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__13);
                    v___x_3731_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3731_, 0, v___x_3729_);
                    lean_ctor_set(v___x_3731_, 1, v___x_3730_);
                    v___x_3732_ = l_Lean_MessageData_ofName(v_mod_3726_);
                    v___x_3733_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3733_, 0, v___x_3731_);
                    lean_ctor_set(v___x_3733_, 1, v___x_3732_);
                    v___x_3734_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__15);
                    v___x_3735_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3735_, 0, v___x_3733_);
                    lean_ctor_set(v___x_3735_, 1, v___x_3734_);
                    v___x_3736_ = l_Lean_MessageData_note(v___x_3735_);
                    v___x_3737_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3737_, 0, v_msg_3693_);
                    lean_ctor_set(v___x_3737_, 1, v___x_3736_);
                    if v_isShared_3722_ == 0 {
                        lean_ctor_set_tag(v___x_3721_, 0);
                        lean_ctor_set(v___x_3721_, 0, v___x_3737_);
                        v___x_3739_ = v___x_3721_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3737_);
                        v___x_3739_ = v_reuseFailAlloc_3740_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3741_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__7);
                    v___x_3742_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3742_, 0, v___x_3741_);
                    lean_ctor_set(v___x_3742_, 1, v_c_3710_);
                    v___x_3743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__17);
                    v___x_3744_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3744_, 0, v___x_3742_);
                    lean_ctor_set(v___x_3744_, 1, v___x_3743_);
                    v___x_3745_ = l_Lean_MessageData_ofName(v_mod_3726_);
                    v___x_3746_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3746_, 0, v___x_3744_);
                    lean_ctor_set(v___x_3746_, 1, v___x_3745_);
                    v___x_3747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__19);
                    v___x_3748_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3748_, 0, v___x_3746_);
                    lean_ctor_set(v___x_3748_, 1, v___x_3747_);
                    v___x_3749_ = l_Lean_MessageData_note(v___x_3748_);
                    v___x_3750_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3750_, 0, v_msg_3693_);
                    lean_ctor_set(v___x_3750_, 1, v___x_3749_);
                    if v_isShared_3722_ == 0 {
                        lean_ctor_set_tag(v___x_3721_, 0);
                        lean_ctor_set(v___x_3721_, 0, v___x_3750_);
                        v___x_3752_ = v___x_3721_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
                        v___x_3752_ = v_reuseFailAlloc_3753_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3739_;
            }
            3 => {
                return v___x_3752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___boxed(
    mut v_msg_3756_: *mut LeanObject,
    mut v_declHint_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3760_: *mut LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_3756_, v_declHint_3757_, v___y_3758_);
    lean_dec(v___y_3758_);
    return v_res_3760_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9(
    mut v_msg_3761_: *mut LeanObject,
    mut v_declHint_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3768_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_3761_, v_declHint_3762_, v___y_3766_);
                v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
                v_isSharedCheck_3778_ = (!lean_is_exclusive(v___x_3768_)) as u8;
                if v_isSharedCheck_3778_ == 0 {
                    v___x_3771_ = v___x_3768_;
                    v_isShared_3772_ = v_isSharedCheck_3778_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3769_);
                    lean_dec(v___x_3768_);
                    v___x_3771_ = lean_box(0);
                    v_isShared_3772_ = v_isSharedCheck_3778_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3773_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3774_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3774_, 0, v___x_3773_);
                lean_ctor_set(v___x_3774_, 1, v_a_3769_);
                if v_isShared_3772_ == 0 {
                    lean_ctor_set(v___x_3771_, 0, v___x_3774_);
                    v___x_3776_ = v___x_3771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
                    v___x_3776_ = v_reuseFailAlloc_3777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9___boxed(
    mut v_msg_3779_: *mut LeanObject,
    mut v_declHint_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
    mut v___y_3782_: *mut LeanObject,
    mut v___y_3783_: *mut LeanObject,
    mut v___y_3784_: *mut LeanObject,
    mut v___y_3785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3786_: *mut LeanObject = core::ptr::null_mut();
    v_res_3786_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9(v_msg_3779_, v_declHint_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
    lean_dec(v___y_3784_);
    lean_dec_ref(v___y_3783_);
    lean_dec(v___y_3782_);
    lean_dec_ref(v___y_3781_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10___redArg(
    mut v_ref_3787_: *mut LeanObject,
    mut v_msg_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3806_: u8 = 0;
    let mut v_cancelTk_x3f_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3808_: u8 = 0;
    let mut v_inheritedTraceOptions_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3794_ = lean_ctor_get(v___y_3791_, 0);
    v_fileMap_3795_ = lean_ctor_get(v___y_3791_, 1);
    v_options_3796_ = lean_ctor_get(v___y_3791_, 2);
    v_currRecDepth_3797_ = lean_ctor_get(v___y_3791_, 3);
    v_maxRecDepth_3798_ = lean_ctor_get(v___y_3791_, 4);
    v_ref_3799_ = lean_ctor_get(v___y_3791_, 5);
    v_currNamespace_3800_ = lean_ctor_get(v___y_3791_, 6);
    v_openDecls_3801_ = lean_ctor_get(v___y_3791_, 7);
    v_initHeartbeats_3802_ = lean_ctor_get(v___y_3791_, 8);
    v_maxHeartbeats_3803_ = lean_ctor_get(v___y_3791_, 9);
    v_quotContext_3804_ = lean_ctor_get(v___y_3791_, 10);
    v_currMacroScope_3805_ = lean_ctor_get(v___y_3791_, 11);
    v_diag_3806_ = lean_ctor_get_uint8(
        v___y_3791_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3807_ = lean_ctor_get(v___y_3791_, 12);
    v_suppressElabErrors_3808_ = lean_ctor_get_uint8(
        v___y_3791_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3809_ = lean_ctor_get(v___y_3791_, 13);
    v_ref_3810_ = l_Lean_replaceRef(v_ref_3787_, v_ref_3799_);
    lean_inc_ref(v_inheritedTraceOptions_3809_);
    lean_inc(v_cancelTk_x3f_3807_);
    lean_inc(v_currMacroScope_3805_);
    lean_inc(v_quotContext_3804_);
    lean_inc(v_maxHeartbeats_3803_);
    lean_inc(v_initHeartbeats_3802_);
    lean_inc(v_openDecls_3801_);
    lean_inc(v_currNamespace_3800_);
    lean_inc(v_maxRecDepth_3798_);
    lean_inc(v_currRecDepth_3797_);
    lean_inc_ref(v_options_3796_);
    lean_inc_ref(v_fileMap_3795_);
    lean_inc_ref(v_fileName_3794_);
    v___x_3811_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3811_, 0, v_fileName_3794_);
    lean_ctor_set(v___x_3811_, 1, v_fileMap_3795_);
    lean_ctor_set(v___x_3811_, 2, v_options_3796_);
    lean_ctor_set(v___x_3811_, 3, v_currRecDepth_3797_);
    lean_ctor_set(v___x_3811_, 4, v_maxRecDepth_3798_);
    lean_ctor_set(v___x_3811_, 5, v_ref_3810_);
    lean_ctor_set(v___x_3811_, 6, v_currNamespace_3800_);
    lean_ctor_set(v___x_3811_, 7, v_openDecls_3801_);
    lean_ctor_set(v___x_3811_, 8, v_initHeartbeats_3802_);
    lean_ctor_set(v___x_3811_, 9, v_maxHeartbeats_3803_);
    lean_ctor_set(v___x_3811_, 10, v_quotContext_3804_);
    lean_ctor_set(v___x_3811_, 11, v_currMacroScope_3805_);
    lean_ctor_set(v___x_3811_, 12, v_cancelTk_x3f_3807_);
    lean_ctor_set(v___x_3811_, 13, v_inheritedTraceOptions_3809_);
    lean_ctor_set_uint8(
        v___x_3811_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3806_,
    );
    lean_ctor_set_uint8(
        v___x_3811_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3808_,
    );
    v___x_3812_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v_msg_3788_, v___y_3789_, v___y_3790_, v___x_3811_, v___y_3792_);
    lean_dec_ref_known(v___x_3811_, 14);
    return v___x_3812_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(
    mut v_ref_3813_: *mut LeanObject,
    mut v_msg_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
    mut v___y_3816_: *mut LeanObject,
    mut v___y_3817_: *mut LeanObject,
    mut v___y_3818_: *mut LeanObject,
    mut v___y_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3820_: *mut LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3813_, v_msg_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
    lean_dec(v___y_3818_);
    lean_dec_ref(v___y_3817_);
    lean_dec(v___y_3816_);
    lean_dec_ref(v___y_3815_);
    lean_dec(v_ref_3813_);
    return v_res_3820_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(
    mut v_ref_3821_: *mut LeanObject,
    mut v_msg_3822_: *mut LeanObject,
    mut v_declHint_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
    mut v___y_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    v___x_3829_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9(v_msg_3822_, v_declHint_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
    v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
    lean_inc(v_a_3830_);
    lean_dec_ref(v___x_3829_);
    v___x_3831_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3821_, v_a_3830_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
    return v___x_3831_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg___boxed(
    mut v_ref_3832_: *mut LeanObject,
    mut v_msg_3833_: *mut LeanObject,
    mut v_declHint_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
    mut v___y_3837_: *mut LeanObject,
    mut v___y_3838_: *mut LeanObject,
    mut v___y_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3840_: *mut LeanObject = core::ptr::null_mut();
    v_res_3840_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3832_, v_msg_3833_, v_declHint_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
    lean_dec(v___y_3838_);
    lean_dec_ref(v___y_3837_);
    lean_dec(v___y_3836_);
    lean_dec_ref(v___y_3835_);
    lean_dec(v_ref_3832_);
    return v_res_3840_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    v___x_3842_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
    return v___x_3843_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    v___x_3845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_3846_ = l_Lean_stringToMessageData(v___x_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(
    mut v_ref_3847_: *mut LeanObject,
    mut v_constName_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
    mut v___y_3850_: *mut LeanObject,
    mut v___y_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u8 = 0;
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    v___x_3854_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_3855_ = 0;
    lean_inc(v_constName_3848_);
    v___x_3856_ = l_Lean_MessageData_ofConstName(v_constName_3848_, v___x_3855_);
    v___x_3857_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3857_, 0, v___x_3854_);
    lean_ctor_set(v___x_3857_, 1, v___x_3856_);
    v___x_3858_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_3859_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3859_, 0, v___x_3857_);
    lean_ctor_set(v___x_3859_, 1, v___x_3858_);
    v___x_3860_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3847_, v___x_3859_, v_constName_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
    return v___x_3860_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_3861_: *mut LeanObject,
    mut v_constName_3862_: *mut LeanObject,
    mut v___y_3863_: *mut LeanObject,
    mut v___y_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3868_: *mut LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_ref_3861_, v_constName_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
    lean_dec(v___y_3866_);
    lean_dec_ref(v___y_3865_);
    lean_dec(v___y_3864_);
    lean_dec_ref(v___y_3863_);
    lean_dec(v_ref_3861_);
    return v_res_3868_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_constName_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3875_ = lean_ctor_get(v___y_3872_, 5);
    v___x_3876_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_ref_3875_, v_constName_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
    return v___x_3876_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_constName_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
    mut v___y_3879_: *mut LeanObject,
    mut v___y_3880_: *mut LeanObject,
    mut v___y_3881_: *mut LeanObject,
    mut v___y_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3883_: *mut LeanObject = core::ptr::null_mut();
    v_res_3883_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
    lean_dec(v___y_3881_);
    lean_dec_ref(v___y_3880_);
    lean_dec(v___y_3879_);
    lean_dec_ref(v___y_3878_);
    return v_res_3883_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0(
    mut v_constName_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: u8 = 0;
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3898_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3890_ = lean_st_ref_get(v___y_3888_);
                v_env_3891_ = lean_ctor_get(v___x_3890_, 0);
                lean_inc_ref(v_env_3891_);
                lean_dec(v___x_3890_);
                v___x_3892_ = 0;
                lean_inc(v_constName_3884_);
                v___x_3893_ =
                    l_Lean_Environment_find_x3f(v_env_3891_, v_constName_3884_, v___x_3892_);
                if lean_obj_tag(v___x_3893_) == 0 {
                    v___x_3894_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
                    return v___x_3894_;
                } else {
                    lean_dec(v_constName_3884_);
                    v_val_3895_ = lean_ctor_get(v___x_3893_, 0);
                    v_isSharedCheck_3902_ = (!lean_is_exclusive(v___x_3893_)) as u8;
                    if v_isSharedCheck_3902_ == 0 {
                        v___x_3897_ = v___x_3893_;
                        v_isShared_3898_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3895_);
                        lean_dec(v___x_3893_);
                        v___x_3897_ = lean_box(0);
                        v_isShared_3898_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3898_ == 0 {
                    lean_ctor_set_tag(v___x_3897_, 0);
                    v___x_3900_ = v___x_3897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_val_3895_);
                    v___x_3900_ = v_reuseFailAlloc_3901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0___boxed(
    mut v_constName_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3909_: *mut LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0(v_constName_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
    lean_dec(v___y_3907_);
    lean_dec_ref(v___y_3906_);
    lean_dec(v___y_3905_);
    lean_dec_ref(v___y_3904_);
    return v_res_3909_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u64 = 0;
    v___x_3916_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_3917_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3916_);
    return v___x_3917_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3918_: u64 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    v___x_3918_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
    v___x_3919_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_3920_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_3920_, 0, v___x_3919_);
    lean_ctor_set_uint64(
        v___x_3920_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3918_,
    );
    return v___x_3920_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    v___x_3921_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3921_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3922_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
    v___x_3923_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3923_, 0, v___x_3922_);
    return v___x_3923_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    v___x_3924_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
    v___x_3925_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3925_, 0, v___x_3924_);
    lean_ctor_set(v___x_3925_, 1, v___x_3924_);
    lean_ctor_set(v___x_3925_, 2, v___x_3924_);
    lean_ctor_set(v___x_3925_, 3, v___x_3924_);
    lean_ctor_set(v___x_3925_, 4, v___x_3924_);
    lean_ctor_set(v___x_3925_, 5, v___x_3924_);
    return v___x_3925_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    v___x_3926_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
    v___x_3927_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3927_, 0, v___x_3926_);
    lean_ctor_set(v___x_3927_, 1, v___x_3926_);
    lean_ctor_set(v___x_3927_, 2, v___x_3926_);
    lean_ctor_set(v___x_3927_, 3, v___x_3926_);
    lean_ctor_set(v___x_3927_, 4, v___x_3926_);
    return v___x_3927_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: u64 = 0;
    v___x_3928_ = 2;
    v___x_3929_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3928_);
    return v___x_3929_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    v___x_3931_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__8_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_3932_ = l_Lean_stringToMessageData(v___x_3931_);
    return v___x_3932_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___x_3935_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__11_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_3936_ = l_Lean_stringToMessageData(v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(
    mut v___x_3937_: *mut LeanObject,
    mut v___x_3938_: *mut LeanObject,
    mut v___x_3939_: *mut LeanObject,
    mut v_decl_3940_: *mut LeanObject,
    mut v_x_3941_: *mut LeanObject,
    mut v_kind_3942_: u8,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: usize = 0;
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3970_: u8 = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3979_: u8 = 0;
    let mut v_ctxApprox_3980_: u8 = 0;
    let mut v_quasiPatternApprox_3981_: u8 = 0;
    let mut v_constApprox_3982_: u8 = 0;
    let mut v_isDefEqStuckEx_3983_: u8 = 0;
    let mut v_unificationHints_3984_: u8 = 0;
    let mut v_proofIrrelevance_3985_: u8 = 0;
    let mut v_assignSyntheticOpaque_3986_: u8 = 0;
    let mut v_offsetCnstrs_3987_: u8 = 0;
    let mut v_etaStruct_3988_: u8 = 0;
    let mut v_univApprox_3989_: u8 = 0;
    let mut v_iota_3990_: u8 = 0;
    let mut v_beta_3991_: u8 = 0;
    let mut v_proj_3992_: u8 = 0;
    let mut v_zeta_3993_: u8 = 0;
    let mut v_zetaDelta_3994_: u8 = 0;
    let mut v_zetaUnused_3995_: u8 = 0;
    let mut v_zetaHave_3996_: u8 = 0;
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: u8 = 0;
    let mut v_config_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: u64 = 0;
    let mut v___x_4006_: u64 = 0;
    let mut v___x_4007_: u64 = 0;
    let mut v___x_4008_: u64 = 0;
    let mut v___x_4009_: u64 = 0;
    let mut v_key_4010_: u64 = 0;
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4019_: u8 = 0;
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: u8 = 0;
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_unused_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4068_: u8 = 0;
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_reuseFailAlloc_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut v_a_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3946_ = 0;
                v___x_3947_ = 1;
                v___x_3948_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v___x_3949_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v___x_3950_ = lean_unsigned_to_nat(32);
                v___x_3951_ = lean_mk_empty_array_with_capacity(v___x_3950_);
                v___x_3952_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__3);
                v___x_3953_ = 5usize;
                lean_inc_n(v___x_3937_, 7);
                v___x_3954_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_3954_, 0, v___x_3952_);
                lean_ctor_set(v___x_3954_, 1, v___x_3951_);
                lean_ctor_set(v___x_3954_, 2, v___x_3937_);
                lean_ctor_set(v___x_3954_, 3, v___x_3937_);
                lean_ctor_set_usize(v___x_3954_, 4, v___x_3953_);
                v___x_3955_ = lean_box(1);
                lean_inc_ref(v___x_3954_);
                v___x_3956_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3956_, 0, v___x_3949_);
                lean_ctor_set(v___x_3956_, 1, v___x_3954_);
                lean_ctor_set(v___x_3956_, 2, v___x_3955_);
                v___x_3957_ = lean_mk_empty_array_with_capacity(v___x_3937_);
                v___x_3958_ = lean_box(0);
                lean_inc_ref(v___x_3957_);
                lean_inc_ref(v___x_3956_);
                lean_inc_n(v___x_3938_, 2);
                v___x_3959_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_3959_, 0, v___x_3948_);
                lean_ctor_set(v___x_3959_, 1, v___x_3938_);
                lean_ctor_set(v___x_3959_, 2, v___x_3956_);
                lean_ctor_set(v___x_3959_, 3, v___x_3957_);
                lean_ctor_set(v___x_3959_, 4, v___x_3958_);
                lean_ctor_set(v___x_3959_, 5, v___x_3937_);
                lean_ctor_set(v___x_3959_, 6, v___x_3958_);
                lean_ctor_set_uint8(
                    v___x_3959_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_3946_,
                );
                lean_ctor_set_uint8(
                    v___x_3959_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_3946_,
                );
                lean_ctor_set_uint8(
                    v___x_3959_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_3946_,
                );
                lean_ctor_set_uint8(
                    v___x_3959_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_3947_,
                );
                v___x_3960_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_3960_, 0, v___x_3937_);
                lean_ctor_set(v___x_3960_, 1, v___x_3937_);
                lean_ctor_set(v___x_3960_, 2, v___x_3937_);
                lean_ctor_set(v___x_3960_, 3, v___x_3937_);
                lean_ctor_set(v___x_3960_, 4, v___x_3949_);
                lean_ctor_set(v___x_3960_, 5, v___x_3949_);
                lean_ctor_set(v___x_3960_, 6, v___x_3949_);
                lean_ctor_set(v___x_3960_, 7, v___x_3949_);
                lean_ctor_set(v___x_3960_, 8, v___x_3949_);
                lean_ctor_set(v___x_3960_, 9, v___x_3949_);
                v___x_3961_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__5_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v___x_3962_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__6_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v___x_3963_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3963_, 0, v___x_3960_);
                lean_ctor_set(v___x_3963_, 1, v___x_3961_);
                lean_ctor_set(v___x_3963_, 2, v___x_3938_);
                lean_ctor_set(v___x_3963_, 3, v___x_3954_);
                lean_ctor_set(v___x_3963_, 4, v___x_3962_);
                v___x_3964_ = lean_st_mk_ref(v___x_3963_);
                lean_inc(v_decl_3940_);
                v___x_3976_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0(v_decl_3940_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                if lean_obj_tag(v___x_3976_) == 0 {
                    v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
                    lean_inc(v_a_3977_);
                    lean_dec_ref_known(v___x_3976_, 1);
                    v___x_3978_ = l_Lean_Meta_Context_config(v___x_3959_);
                    v_foApprox_3979_ = lean_ctor_get_uint8(v___x_3978_, 0 as u32);
                    v_ctxApprox_3980_ = lean_ctor_get_uint8(v___x_3978_, 1 as u32);
                    v_quasiPatternApprox_3981_ = lean_ctor_get_uint8(v___x_3978_, 2 as u32);
                    v_constApprox_3982_ = lean_ctor_get_uint8(v___x_3978_, 3 as u32);
                    v_isDefEqStuckEx_3983_ = lean_ctor_get_uint8(v___x_3978_, 4 as u32);
                    v_unificationHints_3984_ = lean_ctor_get_uint8(v___x_3978_, 5 as u32);
                    v_proofIrrelevance_3985_ = lean_ctor_get_uint8(v___x_3978_, 6 as u32);
                    v_assignSyntheticOpaque_3986_ = lean_ctor_get_uint8(v___x_3978_, 7 as u32);
                    v_offsetCnstrs_3987_ = lean_ctor_get_uint8(v___x_3978_, 8 as u32);
                    v_etaStruct_3988_ = lean_ctor_get_uint8(v___x_3978_, 10 as u32);
                    v_univApprox_3989_ = lean_ctor_get_uint8(v___x_3978_, 11 as u32);
                    v_iota_3990_ = lean_ctor_get_uint8(v___x_3978_, 12 as u32);
                    v_beta_3991_ = lean_ctor_get_uint8(v___x_3978_, 13 as u32);
                    v_proj_3992_ = lean_ctor_get_uint8(v___x_3978_, 14 as u32);
                    v_zeta_3993_ = lean_ctor_get_uint8(v___x_3978_, 15 as u32);
                    v_zetaDelta_3994_ = lean_ctor_get_uint8(v___x_3978_, 16 as u32);
                    v_zetaUnused_3995_ = lean_ctor_get_uint8(v___x_3978_, 17 as u32);
                    v_zetaHave_3996_ = lean_ctor_get_uint8(v___x_3978_, 18 as u32);
                    v_isSharedCheck_4074_ = (!lean_is_exclusive(v___x_3978_)) as u8;
                    if v_isSharedCheck_4074_ == 0 {
                        v___x_3998_ = v___x_3978_;
                        v_isShared_3999_ = v_isSharedCheck_4074_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_3978_);
                        v___x_3998_ = lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4074_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3964_);
                    lean_dec_ref_known(v___x_3959_, 7);
                    lean_dec_ref(v___x_3957_);
                    lean_dec_ref_known(v___x_3956_, 3);
                    lean_dec(v_decl_3940_);
                    lean_dec(v___x_3939_);
                    lean_dec(v___x_3938_);
                    lean_dec(v___x_3937_);
                    v_a_4075_ = lean_ctor_get(v___x_3976_, 0);
                    v_isSharedCheck_4082_ = (!lean_is_exclusive(v___x_3976_)) as u8;
                    if v_isSharedCheck_4082_ == 0 {
                        v___x_4077_ = v___x_3976_;
                        v_isShared_4078_ = v_isSharedCheck_4082_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4075_);
                        lean_dec(v___x_3976_);
                        v___x_4077_ = lean_box(0);
                        v_isShared_4078_ = v_isSharedCheck_4082_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3966_) == 0 {
                    v_a_3967_ = lean_ctor_get(v___y_3966_, 0);
                    v_isSharedCheck_3975_ = (!lean_is_exclusive(v___y_3966_)) as u8;
                    if v_isSharedCheck_3975_ == 0 {
                        v___x_3969_ = v___y_3966_;
                        v_isShared_3970_ = v_isSharedCheck_3975_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3967_);
                        lean_dec(v___y_3966_);
                        v___x_3969_ = lean_box(0);
                        v_isShared_3970_ = v_isSharedCheck_3975_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3964_);
                    return v___y_3966_;
                }
            }
            2 => {
                v___x_3971_ = lean_st_ref_get(v___x_3964_);
                lean_dec(v___x_3964_);
                lean_dec(v___x_3971_);
                if v_isShared_3970_ == 0 {
                    v___x_3973_ = v___x_3969_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3967_);
                    v___x_3973_ = v_reuseFailAlloc_3974_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3973_;
            }
            4 => {
                v___x_4000_ = l_Lean_ConstantInfo_type(v_a_3977_);
                lean_dec(v_a_3977_);
                v___x_4001_ = 0;
                v___x_4002_ = 2;
                if v_isShared_3999_ == 0 {
                    v_config_4004_ = v___x_3998_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 0 as u32, v_foApprox_3979_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 1 as u32, v_ctxApprox_3980_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4073_,
                        2 as u32,
                        v_quasiPatternApprox_3981_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 3 as u32, v_constApprox_3982_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 4 as u32, v_isDefEqStuckEx_3983_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 5 as u32, v_unificationHints_3984_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 6 as u32, v_proofIrrelevance_3985_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4073_,
                        7 as u32,
                        v_assignSyntheticOpaque_3986_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 8 as u32, v_offsetCnstrs_3987_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 10 as u32, v_etaStruct_3988_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 11 as u32, v_univApprox_3989_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 12 as u32, v_iota_3990_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 13 as u32, v_beta_3991_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 14 as u32, v_proj_3992_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 15 as u32, v_zeta_3993_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 16 as u32, v_zetaDelta_3994_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 17 as u32, v_zetaUnused_3995_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4073_, 18 as u32, v_zetaHave_3996_);
                    v_config_4004_ = v_reuseFailAlloc_4073_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(v_config_4004_, 9 as u32, v___x_4002_);
                v___x_4005_ = l_Lean_Meta_Context_configKey(v___x_3959_);
                v___x_4006_ = 3u64;
                v___x_4007_ = lean_uint64_shift_right(v___x_4005_, v___x_4006_);
                v___x_4008_ = lean_uint64_shift_left(v___x_4007_, v___x_4006_);
                v___x_4009_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v_key_4010_ = lean_uint64_lor(v___x_4008_, v___x_4009_);
                v___x_4011_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4011_, 0, v_config_4004_);
                lean_ctor_set_uint64(
                    v___x_4011_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4010_,
                );
                v___x_4012_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4012_, 0, v___x_4011_);
                lean_ctor_set(v___x_4012_, 1, v___x_3938_);
                lean_ctor_set(v___x_4012_, 2, v___x_3956_);
                lean_ctor_set(v___x_4012_, 3, v___x_3957_);
                lean_ctor_set(v___x_4012_, 4, v___x_3958_);
                lean_ctor_set(v___x_4012_, 5, v___x_3937_);
                lean_ctor_set(v___x_4012_, 6, v___x_3958_);
                lean_ctor_set_uint8(
                    v___x_4012_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_3946_,
                );
                lean_ctor_set_uint8(
                    v___x_4012_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_3946_,
                );
                lean_ctor_set_uint8(
                    v___x_4012_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_3946_,
                );
                lean_ctor_set_uint8(
                    v___x_4012_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_3947_,
                );
                lean_inc_ref(v___x_4000_);
                v___x_4013_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v___x_4000_,
                    v___x_3958_,
                    v___x_4001_,
                    v___x_4012_,
                    v___x_3964_,
                    v___y_3943_,
                    v___y_3944_,
                );
                lean_dec_ref_known(v___x_4012_, 7);
                if lean_obj_tag(v___x_4013_) == 0 {
                    v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
                    lean_inc(v_a_4014_);
                    lean_dec_ref_known(v___x_4013_, 1);
                    v_snd_4015_ = lean_ctor_get(v_a_4014_, 1);
                    lean_inc(v_snd_4015_);
                    lean_dec(v_a_4014_);
                    v_snd_4016_ = lean_ctor_get(v_snd_4015_, 1);
                    v_isSharedCheck_4063_ = (!lean_is_exclusive(v_snd_4015_)) as u8;
                    if v_isSharedCheck_4063_ == 0 {
                        v_unused_4064_ = lean_ctor_get(v_snd_4015_, 0);
                        lean_dec(v_unused_4064_);
                        v___x_4018_ = v_snd_4015_;
                        v_isShared_4019_ = v_isSharedCheck_4063_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_4016_);
                        lean_dec(v_snd_4015_);
                        v___x_4018_ = lean_box(0);
                        v_isShared_4019_ = v_isSharedCheck_4063_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4000_);
                    lean_dec(v___x_3964_);
                    lean_dec_ref_known(v___x_3959_, 7);
                    lean_dec(v_decl_3940_);
                    lean_dec(v___x_3939_);
                    v_a_4065_ = lean_ctor_get(v___x_4013_, 0);
                    v_isSharedCheck_4072_ = (!lean_is_exclusive(v___x_4013_)) as u8;
                    if v_isSharedCheck_4072_ == 0 {
                        v___x_4067_ = v___x_4013_;
                        v_isShared_4068_ = v_isSharedCheck_4072_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4065_);
                        lean_dec(v___x_4013_);
                        v___x_4067_ = lean_box(0);
                        v_isShared_4068_ = v_isSharedCheck_4072_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4020_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__9_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v___x_4021_ = lean_unsigned_to_nat(30);
                v___x_4022_ = l_Lean_inlineExprTrailing(v___x_4000_, v___x_4021_);
                if v_isShared_4019_ == 0 {
                    lean_ctor_set_tag(v___x_4018_, 7);
                    lean_ctor_set(v___x_4018_, 1, v___x_4022_);
                    lean_ctor_set(v___x_4018_, 0, v___x_4020_);
                    v___x_4024_ = v___x_4018_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4020_);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4022_);
                    v___x_4024_ = v_reuseFailAlloc_4062_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if lean_obj_tag(v_snd_4016_) == 5 {
                    v_fn_4025_ = lean_ctor_get(v_snd_4016_, 0);
                    lean_inc_ref(v_fn_4025_);
                    if lean_obj_tag(v_fn_4025_) == 5 {
                        v_arg_4026_ = lean_ctor_get(v_snd_4016_, 1);
                        lean_inc_ref(v_arg_4026_);
                        lean_dec_ref_known(v_snd_4016_, 2);
                        v_fn_4027_ = lean_ctor_get(v_fn_4025_, 0);
                        lean_inc_ref_n(v_fn_4027_, 2);
                        v_arg_4028_ = lean_ctor_get(v_fn_4025_, 1);
                        lean_inc_ref(v_arg_4028_);
                        lean_dec_ref_known(v_fn_4025_, 2);
                        v___f_4029_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 7, 2);
                        lean_closure_set(v___f_4029_, 0, v_arg_4028_);
                        lean_closure_set(v___f_4029_, 1, v_arg_4026_);
                        v___x_4030_ = lean_box((v___x_3946_) as usize);
                        v___x_4031_ = lean_box((v_kind_3942_) as usize);
                        v___f_4032_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 12, 6);
                        lean_closure_set(v___f_4032_, 0, v___f_4029_);
                        lean_closure_set(v___f_4032_, 1, v___x_4030_);
                        lean_closure_set(v___f_4032_, 2, v_fn_4027_);
                        lean_closure_set(v___f_4032_, 3, v_decl_3940_);
                        lean_closure_set(v___f_4032_, 4, v___x_4031_);
                        lean_closure_set(v___f_4032_, 5, v___x_4024_);
                        if lean_obj_tag(v_fn_4027_) == 5 {
                            v_fn_4033_ = lean_ctor_get(v_fn_4027_, 0);
                            if lean_obj_tag(v_fn_4033_) == 4 {
                                v_declName_4034_ = lean_ctor_get(v_fn_4033_, 0);
                                if lean_obj_tag(v_declName_4034_) == 1 {
                                    v_pre_4035_ = lean_ctor_get(v_declName_4034_, 0);
                                    if lean_obj_tag(v_pre_4035_) == 0 {
                                        lean_inc_ref(v_declName_4034_);
                                        lean_inc_ref(v_fn_4033_);
                                        v_arg_4036_ = lean_ctor_get(v_fn_4027_, 1);
                                        lean_inc_ref(v_arg_4036_);
                                        lean_dec_ref_known(v_fn_4027_, 2);
                                        v_us_4037_ = lean_ctor_get(v_fn_4033_, 1);
                                        lean_inc(v_us_4037_);
                                        lean_dec_ref_known(v_fn_4033_, 2);
                                        v_str_4038_ = lean_ctor_get(v_declName_4034_, 1);
                                        lean_inc_ref(v_str_4038_);
                                        lean_dec_ref_known(v_declName_4034_, 2);
                                        v___x_4039_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__10_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
                                        v___x_4040_ = lean_string_dec_eq(v_str_4038_, v___x_4039_);
                                        if v___x_4040_ == 0 {
                                            v___x_4041_ = l_Lean_Name_str___override(
                                                v___x_3939_,
                                                v_str_4038_,
                                            );
                                            v___x_4042_ = l_Lean_Expr_const___override(
                                                v___x_4041_,
                                                v_us_4037_,
                                            );
                                            v___x_4043_ = l_Lean_Expr_app___override(
                                                v___x_4042_,
                                                v_arg_4036_,
                                            );
                                            v___x_4044_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v___x_4043_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                            lean_dec_ref_known(v___x_3959_, 7);
                                            lean_dec_ref(v___x_4043_);
                                            v___y_3966_ = v___x_4044_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_str_4038_);
                                            if lean_obj_tag(v_us_4037_) == 1 {
                                                v_tail_4045_ = lean_ctor_get(v_us_4037_, 1);
                                                if lean_obj_tag(v_tail_4045_) == 0 {
                                                    lean_dec_ref_known(v_us_4037_, 2);
                                                    lean_dec_ref(v_arg_4036_);
                                                    lean_dec_ref(v___f_4032_);
                                                    lean_dec(v___x_3939_);
                                                    v___x_4046_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__12_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                                                    v___x_4047_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_4046_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                                    lean_dec_ref_known(v___x_3959_, 7);
                                                    v___y_3966_ = v___x_4047_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_4048_ = l_Lean_Name_str___override(
                                                        v___x_3939_,
                                                        v___x_4039_,
                                                    );
                                                    v___x_4049_ = l_Lean_Expr_const___override(
                                                        v___x_4048_,
                                                        v_us_4037_,
                                                    );
                                                    v___x_4050_ = l_Lean_Expr_app___override(
                                                        v___x_4049_,
                                                        v_arg_4036_,
                                                    );
                                                    v___x_4051_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v___x_4050_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                                    lean_dec_ref_known(v___x_3959_, 7);
                                                    lean_dec_ref(v___x_4050_);
                                                    v___y_3966_ = v___x_4051_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___x_4052_ = l_Lean_Name_str___override(
                                                    v___x_3939_,
                                                    v___x_4039_,
                                                );
                                                v___x_4053_ = l_Lean_Expr_const___override(
                                                    v___x_4052_,
                                                    v_us_4037_,
                                                );
                                                v___x_4054_ = l_Lean_Expr_app___override(
                                                    v___x_4053_,
                                                    v_arg_4036_,
                                                );
                                                v___x_4055_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v___x_4054_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                                lean_dec_ref_known(v___x_3959_, 7);
                                                lean_dec_ref(v___x_4054_);
                                                v___y_3966_ = v___x_4055_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_3939_);
                                        v___x_4056_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v_fn_4027_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                        lean_dec_ref_known(v___x_3959_, 7);
                                        lean_dec_ref_known(v_fn_4027_, 2);
                                        v___y_3966_ = v___x_4056_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_3939_);
                                    v___x_4057_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v_fn_4027_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                    lean_dec_ref_known(v___x_3959_, 7);
                                    lean_dec_ref_known(v_fn_4027_, 2);
                                    v___y_3966_ = v___x_4057_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_3939_);
                                v___x_4058_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v_fn_4027_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                                lean_dec_ref_known(v___x_3959_, 7);
                                lean_dec_ref_known(v_fn_4027_, 2);
                                v___y_3966_ = v___x_4058_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3939_);
                            v___x_4059_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___f_4032_, v_fn_4027_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                            lean_dec_ref_known(v___x_3959_, 7);
                            lean_dec_ref(v_fn_4027_);
                            v___y_3966_ = v___x_4059_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_fn_4025_);
                        lean_dec_ref_known(v_snd_4016_, 2);
                        lean_dec(v_decl_3940_);
                        lean_dec(v___x_3939_);
                        v___x_4060_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_4024_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                        lean_dec_ref_known(v___x_3959_, 7);
                        v___y_3966_ = v___x_4060_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4016_);
                    lean_dec(v_decl_3940_);
                    lean_dec(v___x_3939_);
                    v___x_4061_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_4024_, v___x_3959_, v___x_3964_, v___y_3943_, v___y_3944_);
                    lean_dec_ref_known(v___x_3959_, 7);
                    v___y_3966_ = v___x_4061_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v_isShared_4068_ == 0 {
                    v___x_4070_ = v___x_4067_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
                    v___x_4070_ = v_reuseFailAlloc_4071_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4070_;
            }
            10 => {
                if v_isShared_4078_ == 0 {
                    v___x_4080_ = v___x_4077_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
                    v___x_4080_ = v_reuseFailAlloc_4081_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v___x_4083_: *mut LeanObject,
    mut v___x_4084_: *mut LeanObject,
    mut v___x_4085_: *mut LeanObject,
    mut v_decl_4086_: *mut LeanObject,
    mut v_x_4087_: *mut LeanObject,
    mut v_kind_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4092_: u8 = 0;
    let mut v_res_4093_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4092_ = (lean_unbox(v_kind_4088_) as u8);
    v_res_4093_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___x_4083_, v___x_4084_, v___x_4085_, v_decl_4086_, v_x_4087_, v_kind_boxed_4092_, v___y_4089_, v___y_4090_);
    lean_dec(v___y_4090_);
    lean_dec_ref(v___y_4089_);
    lean_dec(v_x_4087_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4_spec__6(
    mut v_msgData_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    v___x_4098_ = lean_st_ref_get(v___y_4096_);
    v_env_4099_ = lean_ctor_get(v___x_4098_, 0);
    lean_inc_ref(v_env_4099_);
    lean_dec(v___x_4098_);
    v_options_4100_ = lean_ctor_get(v___y_4095_, 2);
    v___x_4101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__2);
    v___x_4102_ = lean_unsigned_to_nat(32);
    v___x_4103_ = lean_mk_empty_array_with_capacity(v___x_4102_);
    lean_dec_ref(v___x_4103_);
    v___x_4104_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg___closed__5);
    lean_inc_ref(v_options_4100_);
    v___x_4105_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4105_, 0, v_env_4099_);
    lean_ctor_set(v___x_4105_, 1, v___x_4101_);
    lean_ctor_set(v___x_4105_, 2, v___x_4104_);
    lean_ctor_set(v___x_4105_, 3, v_options_4100_);
    v___x_4106_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4106_, 0, v___x_4105_);
    lean_ctor_set(v___x_4106_, 1, v_msgData_4094_);
    v___x_4107_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4107_, 0, v___x_4106_);
    return v___x_4107_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4_spec__6___boxed(
    mut v_msgData_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4112_: *mut LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4_spec__6(v_msgData_4108_, v___y_4109_, v___y_4110_);
    lean_dec(v___y_4110_);
    lean_dec_ref(v___y_4109_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4___redArg(
    mut v_msg_4113_: *mut LeanObject,
    mut v___y_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4117_ = lean_ctor_get(v___y_4114_, 5);
                v___x_4118_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4_spec__6(v_msg_4113_, v___y_4114_, v___y_4115_);
                v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
                v_isSharedCheck_4127_ = (!lean_is_exclusive(v___x_4118_)) as u8;
                if v_isSharedCheck_4127_ == 0 {
                    v___x_4121_ = v___x_4118_;
                    v_isShared_4122_ = v_isSharedCheck_4127_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4119_);
                    lean_dec(v___x_4118_);
                    v___x_4121_ = lean_box(0);
                    v_isShared_4122_ = v_isSharedCheck_4127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4117_);
                v___x_4123_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4123_, 0, v_ref_4117_);
                lean_ctor_set(v___x_4123_, 1, v_a_4119_);
                if v_isShared_4122_ == 0 {
                    lean_ctor_set_tag(v___x_4121_, 1);
                    lean_ctor_set(v___x_4121_, 0, v___x_4123_);
                    v___x_4125_ = v___x_4121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
                    v___x_4125_ = v_reuseFailAlloc_4126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4___redArg___boxed(
    mut v_msg_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4132_: *mut LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4___redArg(v_msg_4128_, v___y_4129_, v___y_4130_);
    lean_dec(v___y_4130_);
    lean_dec_ref(v___y_4129_);
    return v_res_4132_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    v___x_4134_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_4135_ = l_Lean_stringToMessageData(v___x_4134_);
    return v___x_4135_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    v___x_4137_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__2_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_4138_ = l_Lean_stringToMessageData(v___x_4137_);
    return v___x_4138_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(
    mut v___x_4139_: *mut LeanObject,
    mut v_decl_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    v___x_4144_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
    v___x_4145_ = l_Lean_MessageData_ofName(v___x_4139_);
    v___x_4146_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4146_, 0, v___x_4144_);
    lean_ctor_set(v___x_4146_, 1, v___x_4145_);
    v___x_4147_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4___closed__3_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
    v___x_4148_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4148_, 0, v___x_4146_);
    lean_ctor_set(v___x_4148_, 1, v___x_4147_);
    v___x_4149_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4___redArg(v___x_4148_, v___y_4141_, v___y_4142_);
    return v___x_4149_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v___x_4150_: *mut LeanObject,
    mut v_decl_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4155_: *mut LeanObject = core::ptr::null_mut();
    v_res_4155_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__4_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_(v___x_4150_, v_decl_4151_, v___y_4152_, v___y_4153_);
    lean_dec(v___y_4153_);
    lean_dec_ref(v___y_4152_);
    lean_dec(v_decl_4151_);
    return v_res_4155_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    v___x_4239_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__31_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_4240_ = l_Lean_registerBuiltinAttribute(v___x_4239_);
    return v___x_4240_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v_a_4241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4242_: *mut LeanObject = core::ptr::null_mut();
    v_res_4242_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_();
    return v_res_4242_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3(
    mut v_00_u03b1_4243_: *mut LeanObject,
    mut v_msg_4244_: *mut LeanObject,
    mut v___y_4245_: *mut LeanObject,
    mut v___y_4246_: *mut LeanObject,
    mut v___y_4247_: *mut LeanObject,
    mut v___y_4248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v_msg_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___boxed(
    mut v_00_u03b1_4251_: *mut LeanObject,
    mut v_msg_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
    mut v___y_4257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4258_: *mut LeanObject = core::ptr::null_mut();
    v_res_4258_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3(v_00_u03b1_4251_, v_msg_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
    lean_dec(v___y_4256_);
    lean_dec_ref(v___y_4255_);
    lean_dec(v___y_4254_);
    lean_dec_ref(v___y_4253_);
    return v_res_4258_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4(
    mut v_00_u03b1_4259_: *mut LeanObject,
    mut v_msg_4260_: *mut LeanObject,
    mut v___y_4261_: *mut LeanObject,
    mut v___y_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    v___x_4264_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4___redArg(v_msg_4260_, v___y_4261_, v___y_4262_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4___boxed(
    mut v_00_u03b1_4265_: *mut LeanObject,
    mut v_msg_4266_: *mut LeanObject,
    mut v___y_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4270_: *mut LeanObject = core::ptr::null_mut();
    v_res_4270_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__4(v_00_u03b1_4265_, v_msg_4266_, v___y_4267_, v___y_4268_);
    lean_dec(v___y_4268_);
    lean_dec_ref(v___y_4267_);
    return v_res_4270_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_4271_: *mut LeanObject,
    mut v_constName_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
    return v___x_4278_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_4279_: *mut LeanObject,
    mut v_constName_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
    mut v___y_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4286_: *mut LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_4279_, v_constName_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
    lean_dec(v___y_4284_);
    lean_dec_ref(v___y_4283_);
    lean_dec(v___y_4282_);
    lean_dec_ref(v___y_4281_);
    return v_res_4286_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3(
    mut v_00_u03b1_4287_: *mut LeanObject,
    mut v_ref_4288_: *mut LeanObject,
    mut v_constName_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    v___x_4295_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_ref_4288_, v_constName_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
    return v___x_4295_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_4296_: *mut LeanObject,
    mut v_ref_4297_: *mut LeanObject,
    mut v_constName_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4304_: *mut LeanObject = core::ptr::null_mut();
    v_res_4304_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_00_u03b1_4296_, v_ref_4297_, v_constName_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
    lean_dec(v___y_4302_);
    lean_dec_ref(v___y_4301_);
    lean_dec(v___y_4300_);
    lean_dec_ref(v___y_4299_);
    lean_dec(v_ref_4297_);
    return v_res_4304_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8(
    mut v_00_u03b1_4305_: *mut LeanObject,
    mut v_ref_4306_: *mut LeanObject,
    mut v_msg_4307_: *mut LeanObject,
    mut v_declHint_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    v___x_4314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(v_ref_4306_, v_msg_4307_, v_declHint_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
    return v___x_4314_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___boxed(
    mut v_00_u03b1_4315_: *mut LeanObject,
    mut v_ref_4316_: *mut LeanObject,
    mut v_msg_4317_: *mut LeanObject,
    mut v_declHint_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4324_: *mut LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8(v_00_u03b1_4315_, v_ref_4316_, v_msg_4317_, v_declHint_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
    lean_dec(v___y_4322_);
    lean_dec_ref(v___y_4321_);
    lean_dec(v___y_4320_);
    lean_dec_ref(v___y_4319_);
    lean_dec(v_ref_4316_);
    return v_res_4324_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10(
    mut v_msg_4325_: *mut LeanObject,
    mut v_declHint_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    v___x_4332_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_4325_, v_declHint_4326_, v___y_4330_);
    return v___x_4332_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10___boxed(
    mut v_msg_4333_: *mut LeanObject,
    mut v_declHint_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4340_: *mut LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__9_spec__10(v_msg_4333_, v_declHint_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
    lean_dec(v___y_4338_);
    lean_dec_ref(v___y_4337_);
    lean_dec(v___y_4336_);
    lean_dec_ref(v___y_4335_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10(
    mut v_00_u03b1_4341_: *mut LeanObject,
    mut v_ref_4342_: *mut LeanObject,
    mut v_msg_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    v___x_4349_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_4342_, v_msg_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
    return v___x_4349_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10___boxed(
    mut v_00_u03b1_4350_: *mut LeanObject,
    mut v_ref_4351_: *mut LeanObject,
    mut v_msg_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4358_: *mut LeanObject = core::ptr::null_mut();
    v_res_4358_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_4350_, v_ref_4351_, v_msg_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
    lean_dec(v___y_4356_);
    lean_dec_ref(v___y_4355_);
    lean_dec(v___y_4354_);
    lean_dec_ref(v___y_4353_);
    lean_dec(v_ref_4351_);
    return v_res_4358_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    v___x_4361_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_4362_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_;
    v___x_4363_ = l_Lean_addBuiltinDocString(v___x_4361_, v___x_4362_);
    return v___x_4363_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2____boxed(
    mut v_a_4364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4365_: *mut LeanObject = core::ptr::null_mut();
    v_res_4365_ = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_();
    return v_res_4365_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0___redArg(
    mut v_e_4366_: *mut LeanObject,
    mut v___y_4367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_unused_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4369_ = l_Lean_Expr_hasMVar(v_e_4366_);
                if v___x_4369_ == 0 {
                    v___x_4370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4370_, 0, v_e_4366_);
                    return v___x_4370_;
                } else {
                    v___x_4371_ = lean_st_ref_get(v___y_4367_);
                    v_mctx_4372_ = lean_ctor_get(v___x_4371_, 0);
                    lean_inc_ref(v_mctx_4372_);
                    lean_dec(v___x_4371_);
                    v___x_4373_ = l_Lean_instantiateMVarsCore(v_mctx_4372_, v_e_4366_);
                    v_fst_4374_ = lean_ctor_get(v___x_4373_, 0);
                    lean_inc(v_fst_4374_);
                    v_snd_4375_ = lean_ctor_get(v___x_4373_, 1);
                    lean_inc(v_snd_4375_);
                    lean_dec_ref(v___x_4373_);
                    v___x_4376_ = lean_st_ref_take(v___y_4367_);
                    v_cache_4377_ = lean_ctor_get(v___x_4376_, 1);
                    v_zetaDeltaFVarIds_4378_ = lean_ctor_get(v___x_4376_, 2);
                    v_postponed_4379_ = lean_ctor_get(v___x_4376_, 3);
                    v_diag_4380_ = lean_ctor_get(v___x_4376_, 4);
                    v_isSharedCheck_4389_ = (!lean_is_exclusive(v___x_4376_)) as u8;
                    if v_isSharedCheck_4389_ == 0 {
                        v_unused_4390_ = lean_ctor_get(v___x_4376_, 0);
                        lean_dec(v_unused_4390_);
                        v___x_4382_ = v___x_4376_;
                        v_isShared_4383_ = v_isSharedCheck_4389_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4380_);
                        lean_inc(v_postponed_4379_);
                        lean_inc(v_zetaDeltaFVarIds_4378_);
                        lean_inc(v_cache_4377_);
                        lean_dec(v___x_4376_);
                        v___x_4382_ = lean_box(0);
                        v_isShared_4383_ = v_isSharedCheck_4389_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4383_ == 0 {
                    lean_ctor_set(v___x_4382_, 0, v_snd_4375_);
                    v___x_4385_ = v___x_4382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_snd_4375_);
                    lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_cache_4377_);
                    lean_ctor_set(v_reuseFailAlloc_4388_, 2, v_zetaDeltaFVarIds_4378_);
                    lean_ctor_set(v_reuseFailAlloc_4388_, 3, v_postponed_4379_);
                    lean_ctor_set(v_reuseFailAlloc_4388_, 4, v_diag_4380_);
                    v___x_4385_ = v_reuseFailAlloc_4388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4386_ = lean_st_ref_set(v___y_4367_, v___x_4385_);
                v___x_4387_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4387_, 0, v_fst_4374_);
                return v___x_4387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0___redArg___boxed(
    mut v_e_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4394_: *mut LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0___redArg(
        v_e_4391_,
        v___y_4392_,
    );
    lean_dec(v___y_4392_);
    return v_res_4394_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0(
    mut v_e_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    v___x_4401_ = l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0___redArg(
        v_e_4395_,
        v___y_4397_,
    );
    return v___x_4401_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0___boxed(
    mut v_e_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4408_: *mut LeanObject = core::ptr::null_mut();
    v_res_4408_ = l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0(
        v_e_4402_,
        v___y_4403_,
        v___y_4404_,
        v___y_4405_,
        v___y_4406_,
    );
    lean_dec(v___y_4406_);
    lean_dec_ref(v___y_4405_);
    lean_dec(v___y_4404_);
    lean_dec_ref(v___y_4403_);
    return v_res_4408_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3___redArg(
    mut v_mvarId_4409_: *mut LeanObject,
    mut v_x_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
    mut v___y_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4420_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4424_: u8 = 0;
    let mut v_a_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4416_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4409_,
                    v_x_4410_,
                    v___y_4411_,
                    v___y_4412_,
                    v___y_4413_,
                    v___y_4414_,
                );
                if lean_obj_tag(v___x_4416_) == 0 {
                    v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
                    v_isSharedCheck_4424_ = (!lean_is_exclusive(v___x_4416_)) as u8;
                    if v_isSharedCheck_4424_ == 0 {
                        v___x_4419_ = v___x_4416_;
                        v_isShared_4420_ = v_isSharedCheck_4424_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4417_);
                        lean_dec(v___x_4416_);
                        v___x_4419_ = lean_box(0);
                        v_isShared_4420_ = v_isSharedCheck_4424_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4425_ = lean_ctor_get(v___x_4416_, 0);
                    v_isSharedCheck_4432_ = (!lean_is_exclusive(v___x_4416_)) as u8;
                    if v_isSharedCheck_4432_ == 0 {
                        v___x_4427_ = v___x_4416_;
                        v_isShared_4428_ = v_isSharedCheck_4432_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4425_);
                        lean_dec(v___x_4416_);
                        v___x_4427_ = lean_box(0);
                        v_isShared_4428_ = v_isSharedCheck_4432_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4420_ == 0 {
                    v___x_4422_ = v___x_4419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
                    v___x_4422_ = v_reuseFailAlloc_4423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4422_;
            }
            3 => {
                if v_isShared_4428_ == 0 {
                    v___x_4430_ = v___x_4427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
                    v___x_4430_ = v_reuseFailAlloc_4431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3___redArg___boxed(
    mut v_mvarId_4433_: *mut LeanObject,
    mut v_x_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4440_: *mut LeanObject = core::ptr::null_mut();
    v_res_4440_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3___redArg(
        v_mvarId_4433_,
        v_x_4434_,
        v___y_4435_,
        v___y_4436_,
        v___y_4437_,
        v___y_4438_,
    );
    lean_dec(v___y_4438_);
    lean_dec_ref(v___y_4437_);
    lean_dec(v___y_4436_);
    lean_dec_ref(v___y_4435_);
    return v_res_4440_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3(
    mut v_00_u03b1_4441_: *mut LeanObject,
    mut v_mvarId_4442_: *mut LeanObject,
    mut v_x_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    v___x_4449_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3___redArg(
        v_mvarId_4442_,
        v_x_4443_,
        v___y_4444_,
        v___y_4445_,
        v___y_4446_,
        v___y_4447_,
    );
    return v___x_4449_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3___boxed(
    mut v_00_u03b1_4450_: *mut LeanObject,
    mut v_mvarId_4451_: *mut LeanObject,
    mut v_x_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4458_: *mut LeanObject = core::ptr::null_mut();
    v_res_4458_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3(
        v_00_u03b1_4450_,
        v_mvarId_4451_,
        v_x_4452_,
        v___y_4453_,
        v___y_4454_,
        v___y_4455_,
        v___y_4456_,
    );
    lean_dec(v___y_4456_);
    lean_dec_ref(v___y_4455_);
    lean_dec(v___y_4454_);
    lean_dec_ref(v___y_4453_);
    return v_res_4458_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_MVarId_applyRfl___lam__0___closed__0;
    v___x_4461_ = l_Lean_stringToMessageData(v___x_4460_);
    return v___x_4461_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_MVarId_applyRfl___lam__0___closed__2;
    v___x_4464_ = l_Lean_stringToMessageData(v___x_4463_);
    return v___x_4464_;
}
pub unsafe fn l_Lean_MVarId_applyRfl___lam__0(
    mut v___x_4465_: *mut LeanObject,
    mut v___x_4466_: *mut LeanObject,
    mut v___y_4467_: *mut LeanObject,
    mut v___y_4468_: *mut LeanObject,
    mut v___y_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v_fst_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4494_: u8 = 0;
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut v_a_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4472_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                    v___x_4465_,
                    v___x_4466_,
                    v___y_4467_,
                    v___y_4468_,
                    v___y_4469_,
                    v___y_4470_,
                );
                if lean_obj_tag(v___x_4472_) == 0 {
                    v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
                    v_isSharedCheck_4495_ = (!lean_is_exclusive(v___x_4472_)) as u8;
                    if v_isSharedCheck_4495_ == 0 {
                        v___x_4475_ = v___x_4472_;
                        v_isShared_4476_ = v_isSharedCheck_4495_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4473_);
                        lean_dec(v___x_4472_);
                        v___x_4475_ = lean_box(0);
                        v_isShared_4476_ = v_isSharedCheck_4495_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4496_ = lean_ctor_get(v___x_4472_, 0);
                    v_isSharedCheck_4503_ = (!lean_is_exclusive(v___x_4472_)) as u8;
                    if v_isSharedCheck_4503_ == 0 {
                        v___x_4498_ = v___x_4472_;
                        v_isShared_4499_ = v_isSharedCheck_4503_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4496_);
                        lean_dec(v___x_4472_);
                        v___x_4498_ = lean_box(0);
                        v_isShared_4499_ = v_isSharedCheck_4503_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4477_ = lean_ctor_get(v_a_4473_, 0);
                v_snd_4478_ = lean_ctor_get(v_a_4473_, 1);
                v_isSharedCheck_4494_ = (!lean_is_exclusive(v_a_4473_)) as u8;
                if v_isSharedCheck_4494_ == 0 {
                    v___x_4480_ = v_a_4473_;
                    v_isShared_4481_ = v_isSharedCheck_4494_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4478_);
                    lean_inc(v_fst_4477_);
                    lean_dec(v_a_4473_);
                    v___x_4480_ = lean_box(0);
                    v_isShared_4481_ = v_isSharedCheck_4494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4482_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__0___closed__1_once),
                    _init_l_Lean_MVarId_applyRfl___lam__0___closed__1,
                );
                v___x_4483_ = l_Lean_indentExpr(v_fst_4477_);
                if v_isShared_4481_ == 0 {
                    lean_ctor_set_tag(v___x_4480_, 7);
                    lean_ctor_set(v___x_4480_, 1, v___x_4483_);
                    lean_ctor_set(v___x_4480_, 0, v___x_4482_);
                    v___x_4485_ = v___x_4480_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4493_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4482_);
                    lean_ctor_set(v_reuseFailAlloc_4493_, 1, v___x_4483_);
                    v___x_4485_ = v_reuseFailAlloc_4493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4486_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_applyRfl___lam__0___closed__3,
                );
                v___x_4487_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4487_, 0, v___x_4485_);
                lean_ctor_set(v___x_4487_, 1, v___x_4486_);
                v___x_4488_ = l_Lean_indentExpr(v_snd_4478_);
                v___x_4489_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4489_, 0, v___x_4487_);
                lean_ctor_set(v___x_4489_, 1, v___x_4488_);
                if v_isShared_4476_ == 0 {
                    lean_ctor_set(v___x_4475_, 0, v___x_4489_);
                    v___x_4491_ = v___x_4475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
                    v___x_4491_ = v_reuseFailAlloc_4492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4491_;
            }
            5 => {
                if v_isShared_4499_ == 0 {
                    v___x_4501_ = v___x_4498_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
                    v___x_4501_ = v_reuseFailAlloc_4502_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyRfl___lam__0___boxed(
    mut v___x_4504_: *mut LeanObject,
    mut v___x_4505_: *mut LeanObject,
    mut v___y_4506_: *mut LeanObject,
    mut v___y_4507_: *mut LeanObject,
    mut v___y_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4511_: *mut LeanObject = core::ptr::null_mut();
    v_res_4511_ = l_Lean_MVarId_applyRfl___lam__0(
        v___x_4504_,
        v___x_4505_,
        v___y_4506_,
        v___y_4507_,
        v___y_4508_,
        v___y_4509_,
    );
    lean_dec(v___y_4509_);
    lean_dec_ref(v___y_4508_);
    lean_dec(v___y_4507_);
    lean_dec_ref(v___y_4506_);
    return v_res_4511_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_4512_: *mut LeanObject,
    mut v_x_4513_: *mut LeanObject,
    mut v_x_4514_: *mut LeanObject,
    mut v_x_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4520_: u8 = 0;
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: u8 = 0;
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4516_ = lean_ctor_get(v_x_4512_, 0);
                v_vs_4517_ = lean_ctor_get(v_x_4512_, 1);
                v_isSharedCheck_4541_ = (!lean_is_exclusive(v_x_4512_)) as u8;
                if v_isSharedCheck_4541_ == 0 {
                    v___x_4519_ = v_x_4512_;
                    v_isShared_4520_ = v_isSharedCheck_4541_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4517_);
                    lean_inc(v_ks_4516_);
                    lean_dec(v_x_4512_);
                    v___x_4519_ = lean_box(0);
                    v_isShared_4520_ = v_isSharedCheck_4541_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4521_ = lean_array_get_size(v_ks_4516_);
                v___x_4522_ = lean_nat_dec_lt(v_x_4513_, v___x_4521_);
                if v___x_4522_ == 0 {
                    lean_dec(v_x_4513_);
                    v___x_4523_ = lean_array_push(v_ks_4516_, v_x_4514_);
                    v___x_4524_ = lean_array_push(v_vs_4517_, v_x_4515_);
                    if v_isShared_4520_ == 0 {
                        lean_ctor_set(v___x_4519_, 1, v___x_4524_);
                        lean_ctor_set(v___x_4519_, 0, v___x_4523_);
                        v___x_4526_ = v___x_4519_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4523_);
                        lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4524_);
                        v___x_4526_ = v_reuseFailAlloc_4527_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4528_ = lean_array_fget_borrowed(v_ks_4516_, v_x_4513_);
                    v___x_4529_ = l_Lean_instBEqMVarId_beq(v_x_4514_, v_k_x27_4528_);
                    if v___x_4529_ == 0 {
                        if v_isShared_4520_ == 0 {
                            v___x_4531_ = v___x_4519_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_ks_4516_);
                            lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_vs_4517_);
                            v___x_4531_ = v_reuseFailAlloc_4535_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4536_ = lean_array_fset(v_ks_4516_, v_x_4513_, v_x_4514_);
                        v___x_4537_ = lean_array_fset(v_vs_4517_, v_x_4513_, v_x_4515_);
                        lean_dec(v_x_4513_);
                        if v_isShared_4520_ == 0 {
                            lean_ctor_set(v___x_4519_, 1, v___x_4537_);
                            lean_ctor_set(v___x_4519_, 0, v___x_4536_);
                            v___x_4539_ = v___x_4519_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4536_);
                            lean_ctor_set(v_reuseFailAlloc_4540_, 1, v___x_4537_);
                            v___x_4539_ = v_reuseFailAlloc_4540_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4526_;
            }
            3 => {
                v___x_4532_ = lean_unsigned_to_nat(1);
                v___x_4533_ = lean_nat_add(v_x_4513_, v___x_4532_);
                lean_dec(v_x_4513_);
                v_x_4512_ = v___x_4531_;
                v_x_4513_ = v___x_4533_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5___redArg(
    mut v_n_4542_: *mut LeanObject,
    mut v_k_4543_: *mut LeanObject,
    mut v_v_4544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    v___x_4545_ = lean_unsigned_to_nat(0);
    v___x_4546_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_n_4542_, v___x_4545_, v_k_4543_, v_v_4544_);
    return v___x_4546_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    v___x_4547_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4547_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg(
    mut v_x_4548_: *mut LeanObject,
    mut v_x_4549_: usize,
    mut v_x_4550_: usize,
    mut v_x_4551_: *mut LeanObject,
    mut v_x_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: usize = 0;
    let mut v___x_4555_: usize = 0;
    let mut v___x_4556_: usize = 0;
    let mut v___x_4557_: usize = 0;
    let mut v_j_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v_v_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4578_: u8 = 0;
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut v_node_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4589_: usize = 0;
    let mut v___x_4590_: usize = 0;
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4597_: u8 = 0;
    let mut v_unused_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4603_: u8 = 0;
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4608_: u8 = 0;
    let mut v_ks_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: usize = 0;
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v_reuseFailAlloc_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4548_) == 0 {
                    v_es_4553_ = lean_ctor_get(v_x_4548_, 0);
                    v___x_4554_ = 5usize;
                    v___x_4555_ = 1usize;
                    v___x_4556_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4557_ = lean_usize_land(v_x_4549_, v___x_4556_);
                    v_j_4558_ = lean_usize_to_nat(v___x_4557_);
                    v___x_4559_ = lean_array_get_size(v_es_4553_);
                    v___x_4560_ = lean_nat_dec_lt(v_j_4558_, v___x_4559_);
                    if v___x_4560_ == 0 {
                        lean_dec(v_j_4558_);
                        lean_dec(v_x_4552_);
                        lean_dec(v_x_4551_);
                        return v_x_4548_;
                    } else {
                        lean_inc_ref(v_es_4553_);
                        v_isSharedCheck_4597_ = (!lean_is_exclusive(v_x_4548_)) as u8;
                        if v_isSharedCheck_4597_ == 0 {
                            v_unused_4598_ = lean_ctor_get(v_x_4548_, 0);
                            lean_dec(v_unused_4598_);
                            v___x_4562_ = v_x_4548_;
                            v_isShared_4563_ = v_isSharedCheck_4597_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4548_);
                            v___x_4562_ = lean_box(0);
                            v_isShared_4563_ = v_isSharedCheck_4597_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4599_ = lean_ctor_get(v_x_4548_, 0);
                    v_vs_4600_ = lean_ctor_get(v_x_4548_, 1);
                    v_isSharedCheck_4620_ = (!lean_is_exclusive(v_x_4548_)) as u8;
                    if v_isSharedCheck_4620_ == 0 {
                        v___x_4602_ = v_x_4548_;
                        v_isShared_4603_ = v_isSharedCheck_4620_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4600_);
                        lean_inc(v_ks_4599_);
                        lean_dec(v_x_4548_);
                        v___x_4602_ = lean_box(0);
                        v_isShared_4603_ = v_isSharedCheck_4620_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4564_ = lean_array_fget(v_es_4553_, v_j_4558_);
                v___x_4565_ = lean_box(0);
                v_xs_x27_4566_ = lean_array_fset(v_es_4553_, v_j_4558_, v___x_4565_);
                match lean_obj_tag(v_v_4564_) {
                    0 => {
                        v_key_4573_ = lean_ctor_get(v_v_4564_, 0);
                        v_val_4574_ = lean_ctor_get(v_v_4564_, 1);
                        v_isSharedCheck_4584_ = (!lean_is_exclusive(v_v_4564_)) as u8;
                        if v_isSharedCheck_4584_ == 0 {
                            v___x_4576_ = v_v_4564_;
                            v_isShared_4577_ = v_isSharedCheck_4584_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4574_);
                            lean_inc(v_key_4573_);
                            lean_dec(v_v_4564_);
                            v___x_4576_ = lean_box(0);
                            v_isShared_4577_ = v_isSharedCheck_4584_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4585_ = lean_ctor_get(v_v_4564_, 0);
                        v_isSharedCheck_4595_ = (!lean_is_exclusive(v_v_4564_)) as u8;
                        if v_isSharedCheck_4595_ == 0 {
                            v___x_4587_ = v_v_4564_;
                            v_isShared_4588_ = v_isSharedCheck_4595_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4585_);
                            lean_dec(v_v_4564_);
                            v___x_4587_ = lean_box(0);
                            v_isShared_4588_ = v_isSharedCheck_4595_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4596_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4596_, 0, v_x_4551_);
                        lean_ctor_set(v___x_4596_, 1, v_x_4552_);
                        v___y_4568_ = v___x_4596_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4569_ = lean_array_fset(v_xs_x27_4566_, v_j_4558_, v___y_4568_);
                lean_dec(v_j_4558_);
                if v_isShared_4563_ == 0 {
                    lean_ctor_set(v___x_4562_, 0, v___x_4569_);
                    v___x_4571_ = v___x_4562_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4569_);
                    v___x_4571_ = v_reuseFailAlloc_4572_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4571_;
            }
            4 => {
                v___x_4578_ = l_Lean_instBEqMVarId_beq(v_x_4551_, v_key_4573_);
                if v___x_4578_ == 0 {
                    lean_del_object(v___x_4576_);
                    v___x_4579_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4573_,
                        v_val_4574_,
                        v_x_4551_,
                        v_x_4552_,
                    );
                    v___x_4580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4580_, 0, v___x_4579_);
                    v___y_4568_ = v___x_4580_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4574_);
                    lean_dec(v_key_4573_);
                    if v_isShared_4577_ == 0 {
                        lean_ctor_set(v___x_4576_, 1, v_x_4552_);
                        lean_ctor_set(v___x_4576_, 0, v_x_4551_);
                        v___x_4582_ = v___x_4576_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_x_4551_);
                        lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_x_4552_);
                        v___x_4582_ = v_reuseFailAlloc_4583_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4568_ = v___x_4582_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4589_ = lean_usize_shift_right(v_x_4549_, v___x_4554_);
                v___x_4590_ = lean_usize_add(v_x_4550_, v___x_4555_);
                v___x_4591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg(v_node_4585_, v___x_4589_, v___x_4590_, v_x_4551_, v_x_4552_);
                if v_isShared_4588_ == 0 {
                    lean_ctor_set(v___x_4587_, 0, v___x_4591_);
                    v___x_4593_ = v___x_4587_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4591_);
                    v___x_4593_ = v_reuseFailAlloc_4594_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4568_ = v___x_4593_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4603_ == 0 {
                    v___x_4605_ = v___x_4602_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_ks_4599_);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 1, v_vs_4600_);
                    v___x_4605_ = v_reuseFailAlloc_4619_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4606_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5___redArg(v___x_4605_, v_x_4551_, v_x_4552_);
                v___x_4614_ = 7usize;
                v___x_4615_ = lean_usize_dec_le(v___x_4614_, v_x_4550_);
                if v___x_4615_ == 0 {
                    v___x_4616_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4606_);
                    v___x_4617_ = lean_unsigned_to_nat(4);
                    v___x_4618_ = lean_nat_dec_lt(v___x_4616_, v___x_4617_);
                    lean_dec(v___x_4616_);
                    v___y_4608_ = v___x_4618_;
                    state = 10;
                    continue;
                } else {
                    v___y_4608_ = v___x_4615_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4608_ == 0 {
                    v_ks_4609_ = lean_ctor_get(v_newNode_4606_, 0);
                    lean_inc_ref(v_ks_4609_);
                    v_vs_4610_ = lean_ctor_get(v_newNode_4606_, 1);
                    lean_inc_ref(v_vs_4610_);
                    lean_dec_ref(v_newNode_4606_);
                    v___x_4611_ = lean_unsigned_to_nat(0);
                    v___x_4612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___closed__0);
                    v___x_4613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6___redArg(v_x_4550_, v_ks_4609_, v_vs_4610_, v___x_4611_, v___x_4612_);
                    lean_dec_ref(v_vs_4610_);
                    lean_dec_ref(v_ks_4609_);
                    return v___x_4613_;
                } else {
                    return v_newNode_4606_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6___redArg(
    mut v_depth_4621_: usize,
    mut v_keys_4622_: *mut LeanObject,
    mut v_vals_4623_: *mut LeanObject,
    mut v_i_4624_: *mut LeanObject,
    mut v_entries_4625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: u8 = 0;
    let mut v_k_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: u64 = 0;
    let mut v_h_4631_: usize = 0;
    let mut v___x_4632_: usize = 0;
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: usize = 0;
    let mut v_h_4637_: usize = 0;
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4626_ = lean_array_get_size(v_keys_4622_);
                v___x_4627_ = lean_nat_dec_lt(v_i_4624_, v___x_4626_);
                if v___x_4627_ == 0 {
                    lean_dec(v_i_4624_);
                    return v_entries_4625_;
                } else {
                    v_k_4628_ = lean_array_fget_borrowed(v_keys_4622_, v_i_4624_);
                    v_v_4629_ = lean_array_fget_borrowed(v_vals_4623_, v_i_4624_);
                    v___x_4630_ = l_Lean_instHashableMVarId_hash(v_k_4628_);
                    v_h_4631_ = lean_uint64_to_usize(v___x_4630_);
                    v___x_4632_ = 5usize;
                    v___x_4633_ = lean_unsigned_to_nat(1);
                    v___x_4634_ = 1usize;
                    v___x_4635_ = lean_usize_sub(v_depth_4621_, v___x_4634_);
                    v___x_4636_ = lean_usize_mul(v___x_4632_, v___x_4635_);
                    v_h_4637_ = lean_usize_shift_right(v_h_4631_, v___x_4636_);
                    v___x_4638_ = lean_nat_add(v_i_4624_, v___x_4633_);
                    lean_dec(v_i_4624_);
                    lean_inc(v_v_4629_);
                    lean_inc(v_k_4628_);
                    v___x_4639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg(v_entries_4625_, v_h_4637_, v_depth_4621_, v_k_4628_, v_v_4629_);
                    v_i_4624_ = v___x_4638_;
                    v_entries_4625_ = v___x_4639_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_depth_4641_: *mut LeanObject,
    mut v_keys_4642_: *mut LeanObject,
    mut v_vals_4643_: *mut LeanObject,
    mut v_i_4644_: *mut LeanObject,
    mut v_entries_4645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4646_: usize = 0;
    let mut v_res_4647_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4646_ = lean_unbox_usize(v_depth_4641_);
    lean_dec(v_depth_4641_);
    v_res_4647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_boxed_4646_, v_keys_4642_, v_vals_4643_, v_i_4644_, v_entries_4645_);
    lean_dec_ref(v_vals_4643_);
    lean_dec_ref(v_keys_4642_);
    return v_res_4647_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_4648_: *mut LeanObject,
    mut v_x_4649_: *mut LeanObject,
    mut v_x_4650_: *mut LeanObject,
    mut v_x_4651_: *mut LeanObject,
    mut v_x_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_12558__boxed_4653_: usize = 0;
    let mut v_x_12559__boxed_4654_: usize = 0;
    let mut v_res_4655_: *mut LeanObject = core::ptr::null_mut();
    v_x_12558__boxed_4653_ = lean_unbox_usize(v_x_4649_);
    lean_dec(v_x_4649_);
    v_x_12559__boxed_4654_ = lean_unbox_usize(v_x_4650_);
    lean_dec(v_x_4650_);
    v_res_4655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg(v_x_4648_, v_x_12558__boxed_4653_, v_x_12559__boxed_4654_, v_x_4651_, v_x_4652_);
    return v_res_4655_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2___redArg(
    mut v_x_4656_: *mut LeanObject,
    mut v_x_4657_: *mut LeanObject,
    mut v_x_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4659_: u64 = 0;
    let mut v___x_4660_: usize = 0;
    let mut v___x_4661_: usize = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    v___x_4659_ = l_Lean_instHashableMVarId_hash(v_x_4657_);
    v___x_4660_ = lean_uint64_to_usize(v___x_4659_);
    v___x_4661_ = 1usize;
    v___x_4662_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg(v_x_4656_, v___x_4660_, v___x_4661_, v_x_4657_, v_x_4658_);
    return v___x_4662_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2___redArg(
    mut v_mvarId_4663_: *mut LeanObject,
    mut v_val_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v_depth_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4688_: u8 = 0;
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4699_: u8 = 0;
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4667_ = lean_st_ref_take(v___y_4665_);
                v_mctx_4668_ = lean_ctor_get(v___x_4667_, 0);
                v_cache_4669_ = lean_ctor_get(v___x_4667_, 1);
                v_zetaDeltaFVarIds_4670_ = lean_ctor_get(v___x_4667_, 2);
                v_postponed_4671_ = lean_ctor_get(v___x_4667_, 3);
                v_diag_4672_ = lean_ctor_get(v___x_4667_, 4);
                v_isSharedCheck_4700_ = (!lean_is_exclusive(v___x_4667_)) as u8;
                if v_isSharedCheck_4700_ == 0 {
                    v___x_4674_ = v___x_4667_;
                    v_isShared_4675_ = v_isSharedCheck_4700_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_4672_);
                    lean_inc(v_postponed_4671_);
                    lean_inc(v_zetaDeltaFVarIds_4670_);
                    lean_inc(v_cache_4669_);
                    lean_inc(v_mctx_4668_);
                    lean_dec(v___x_4667_);
                    v___x_4674_ = lean_box(0);
                    v_isShared_4675_ = v_isSharedCheck_4700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4676_ = lean_ctor_get(v_mctx_4668_, 0);
                v_levelAssignDepth_4677_ = lean_ctor_get(v_mctx_4668_, 1);
                v_lmvarCounter_4678_ = lean_ctor_get(v_mctx_4668_, 2);
                v_mvarCounter_4679_ = lean_ctor_get(v_mctx_4668_, 3);
                v_lDecls_4680_ = lean_ctor_get(v_mctx_4668_, 4);
                v_decls_4681_ = lean_ctor_get(v_mctx_4668_, 5);
                v_userNames_4682_ = lean_ctor_get(v_mctx_4668_, 6);
                v_lAssignment_4683_ = lean_ctor_get(v_mctx_4668_, 7);
                v_eAssignment_4684_ = lean_ctor_get(v_mctx_4668_, 8);
                v_dAssignment_4685_ = lean_ctor_get(v_mctx_4668_, 9);
                v_isSharedCheck_4699_ = (!lean_is_exclusive(v_mctx_4668_)) as u8;
                if v_isSharedCheck_4699_ == 0 {
                    v___x_4687_ = v_mctx_4668_;
                    v_isShared_4688_ = v_isSharedCheck_4699_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_4685_);
                    lean_inc(v_eAssignment_4684_);
                    lean_inc(v_lAssignment_4683_);
                    lean_inc(v_userNames_4682_);
                    lean_inc(v_decls_4681_);
                    lean_inc(v_lDecls_4680_);
                    lean_inc(v_mvarCounter_4679_);
                    lean_inc(v_lmvarCounter_4678_);
                    lean_inc(v_levelAssignDepth_4677_);
                    lean_inc(v_depth_4676_);
                    lean_dec(v_mctx_4668_);
                    v___x_4687_ = lean_box(0);
                    v_isShared_4688_ = v_isSharedCheck_4699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4689_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2___redArg(v_eAssignment_4684_, v_mvarId_4663_, v_val_4664_);
                if v_isShared_4688_ == 0 {
                    lean_ctor_set(v___x_4687_, 8, v___x_4689_);
                    v___x_4691_ = v___x_4687_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_depth_4676_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_levelAssignDepth_4677_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_lmvarCounter_4678_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 3, v_mvarCounter_4679_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 4, v_lDecls_4680_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 5, v_decls_4681_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 6, v_userNames_4682_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 7, v_lAssignment_4683_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 8, v___x_4689_);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 9, v_dAssignment_4685_);
                    v___x_4691_ = v_reuseFailAlloc_4698_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4675_ == 0 {
                    lean_ctor_set(v___x_4674_, 0, v___x_4691_);
                    v___x_4693_ = v___x_4674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4691_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_cache_4669_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_zetaDeltaFVarIds_4670_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_postponed_4671_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_diag_4672_);
                    v___x_4693_ = v_reuseFailAlloc_4697_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4694_ = lean_st_ref_set(v___y_4665_, v___x_4693_);
                v___x_4695_ = lean_box(0);
                v___x_4696_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4696_, 0, v___x_4695_);
                return v___x_4696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2___redArg___boxed(
    mut v_mvarId_4701_: *mut LeanObject,
    mut v_val_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4705_: *mut LeanObject = core::ptr::null_mut();
    v_res_4705_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2___redArg(
        v_mvarId_4701_,
        v_val_4702_,
        v___y_4703_,
    );
    lean_dec(v___y_4703_);
    return v_res_4705_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    v___x_4707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__0;
    v___x_4708_ = l_Lean_stringToMessageData(v___x_4707_);
    return v___x_4708_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    v___x_4714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__4;
    v___x_4715_ = l_Lean_stringToMessageData(v___x_4714_);
    return v___x_4715_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1(
    mut v_a_4718_: *mut LeanObject,
    mut v___x_4719_: u8,
    mut v_goal_4720_: *mut LeanObject,
    mut v_as_4721_: *mut LeanObject,
    mut v_sz_4722_: usize,
    mut v_i_4723_: usize,
    mut v_b_4724_: *mut LeanObject,
    mut v___y_4725_: *mut LeanObject,
    mut v___y_4726_: *mut LeanObject,
    mut v___y_4727_: *mut LeanObject,
    mut v___y_4728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4730_: u8 = 0;
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4735_: u8 = 0;
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4743_: u8 = 0;
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: usize = 0;
    let mut v___x_4747_: usize = 0;
    let mut v_reuseFailAlloc_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut v_unused_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4755_: u8 = 0;
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v___y_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4762_: u8 = 0;
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4778_: u8 = 0;
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    let mut v___x_4787_: u8 = 0;
    let mut v_a_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4793_: u8 = 0;
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4822_: u8 = 0;
    let mut v_a_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut v_a_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4827_: u8 = 0;
    let mut v_unused_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4730_ = lean_usize_dec_lt(v_i_4723_, v_sz_4722_);
                if v___x_4730_ == 0 {
                    lean_dec(v_goal_4720_);
                    v___x_4731_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4731_, 0, v_b_4724_);
                    return v___x_4731_;
                } else {
                    v_snd_4732_ = lean_ctor_get(v_b_4724_, 1);
                    v_isSharedCheck_4827_ = (!lean_is_exclusive(v_b_4724_)) as u8;
                    if v_isSharedCheck_4827_ == 0 {
                        v_unused_4828_ = lean_ctor_get(v_b_4724_, 0);
                        lean_dec(v_unused_4828_);
                        v___x_4734_ = v_b_4724_;
                        v_isShared_4735_ = v_isSharedCheck_4827_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4732_);
                        lean_dec(v_b_4724_);
                        v___x_4734_ = lean_box(0);
                        v_isShared_4735_ = v_isSharedCheck_4827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4736_ = lean_box(0);
                v_a_4788_ = lean_array_uget_borrowed(v_as_4721_, v_i_4723_);
                lean_inc(v_a_4788_);
                v___x_4789_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v_a_4788_,
                    v___y_4725_,
                    v___y_4726_,
                    v___y_4727_,
                    v___y_4728_,
                );
                if lean_obj_tag(v___x_4789_) == 0 {
                    v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
                    v_isSharedCheck_4825_ = (!lean_is_exclusive(v___x_4789_)) as u8;
                    if v_isSharedCheck_4825_ == 0 {
                        v___x_4792_ = v___x_4789_;
                        v_isShared_4793_ = v_isSharedCheck_4825_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4790_);
                        lean_dec(v___x_4789_);
                        v___x_4792_ = lean_box(0);
                        v_isShared_4793_ = v_isSharedCheck_4825_;
                        state = 13;
                        continue;
                    }
                } else {
                    v_a_4826_ = lean_ctor_get(v___x_4789_, 0);
                    lean_inc(v_a_4826_);
                    lean_dec_ref_known(v___x_4789_, 1);
                    v_a_4785_ = v_a_4826_;
                    state = 12;
                    continue;
                }
            }
            2 => {
                v___x_4739_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_a_4718_, v___y_4726_, v___y_4728_);
                if lean_obj_tag(v___x_4739_) == 0 {
                    lean_dec_ref_known(v___x_4739_, 1);
                    v_snd_4740_ = lean_ctor_get(v_a_4738_, 1);
                    v_isSharedCheck_4750_ = (!lean_is_exclusive(v_a_4738_)) as u8;
                    if v_isSharedCheck_4750_ == 0 {
                        v_unused_4751_ = lean_ctor_get(v_a_4738_, 0);
                        lean_dec(v_unused_4751_);
                        v___x_4742_ = v_a_4738_;
                        v_isShared_4743_ = v_isSharedCheck_4750_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_4740_);
                        lean_dec(v_a_4738_);
                        v___x_4742_ = lean_box(0);
                        v_isShared_4743_ = v_isSharedCheck_4750_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4738_);
                    lean_dec(v_goal_4720_);
                    v_a_4752_ = lean_ctor_get(v___x_4739_, 0);
                    v_isSharedCheck_4759_ = (!lean_is_exclusive(v___x_4739_)) as u8;
                    if v_isSharedCheck_4759_ == 0 {
                        v___x_4754_ = v___x_4739_;
                        v_isShared_4755_ = v_isSharedCheck_4759_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4752_);
                        lean_dec(v___x_4739_);
                        v___x_4754_ = lean_box(0);
                        v_isShared_4755_ = v_isSharedCheck_4759_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4743_ == 0 {
                    lean_ctor_set(v___x_4742_, 0, v___x_4736_);
                    v___x_4745_ = v___x_4742_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4736_);
                    lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_snd_4740_);
                    v___x_4745_ = v_reuseFailAlloc_4749_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4746_ = 1usize;
                v___x_4747_ = lean_usize_add(v_i_4723_, v___x_4746_);
                v_i_4723_ = v___x_4747_;
                v_b_4724_ = v___x_4745_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_4755_ == 0 {
                    v___x_4757_ = v___x_4754_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
                    v___x_4757_ = v_reuseFailAlloc_4758_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4757_;
            }
            7 => {
                if v___y_4762_ == 0 {
                    if lean_obj_tag(v_snd_4732_) == 0 {
                        v___x_4763_ = l_Lean_Meta_saveState___redArg(v___y_4726_, v___y_4728_);
                        if lean_obj_tag(v___x_4763_) == 0 {
                            v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
                            lean_inc(v_a_4764_);
                            lean_dec_ref_known(v___x_4763_, 1);
                            if v_isShared_4735_ == 0 {
                                lean_ctor_set(v___x_4734_, 1, v___y_4761_);
                                lean_ctor_set(v___x_4734_, 0, v_a_4764_);
                                v___x_4766_ = v___x_4734_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
                                lean_ctor_set(v_reuseFailAlloc_4770_, 1, v___y_4761_);
                                v___x_4766_ = v_reuseFailAlloc_4770_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___y_4761_);
                            lean_del_object(v___x_4734_);
                            lean_dec(v_goal_4720_);
                            v_a_4771_ = lean_ctor_get(v___x_4763_, 0);
                            v_isSharedCheck_4778_ = (!lean_is_exclusive(v___x_4763_)) as u8;
                            if v_isSharedCheck_4778_ == 0 {
                                v___x_4773_ = v___x_4763_;
                                v_isShared_4774_ = v_isSharedCheck_4778_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_4771_);
                                lean_dec(v___x_4763_);
                                v___x_4773_ = lean_box(0);
                                v_isShared_4774_ = v_isSharedCheck_4778_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_4761_);
                        v___x_4779_ = lean_box(0);
                        if v_isShared_4735_ == 0 {
                            lean_ctor_set(v___x_4734_, 0, v___x_4779_);
                            v___x_4781_ = v___x_4734_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
                            lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_snd_4732_);
                            v___x_4781_ = v_reuseFailAlloc_4782_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4734_);
                    lean_dec(v_snd_4732_);
                    lean_dec(v_goal_4720_);
                    v___x_4783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4783_, 0, v___y_4761_);
                    return v___x_4783_;
                }
            }
            8 => {
                v___x_4767_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4767_, 0, v___x_4766_);
                v___x_4768_ = lean_box(0);
                v___x_4769_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4769_, 0, v___x_4768_);
                lean_ctor_set(v___x_4769_, 1, v___x_4767_);
                v_a_4738_ = v___x_4769_;
                state = 2;
                continue;
            }
            9 => {
                if v_isShared_4774_ == 0 {
                    v___x_4776_ = v___x_4773_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
                    v___x_4776_ = v_reuseFailAlloc_4777_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4776_;
            }
            11 => {
                v_a_4738_ = v___x_4781_;
                state = 2;
                continue;
            }
            12 => {
                v___x_4786_ = l_Lean_Exception_isInterrupt(v_a_4785_);
                if v___x_4786_ == 0 {
                    lean_inc_ref(v_a_4785_);
                    v___x_4787_ = l_Lean_Exception_isRuntime(v_a_4785_);
                    v___y_4761_ = v_a_4785_;
                    v___y_4762_ = v___x_4787_;
                    state = 7;
                    continue;
                } else {
                    v___y_4761_ = v_a_4785_;
                    v___y_4762_ = v___x_4786_;
                    state = 7;
                    continue;
                }
            }
            13 => {
                v___x_4794_ = 0;
                v___x_4795_ = lean_alloc_ctor(0, 0, (4) as u32);
                lean_ctor_set_uint8(v___x_4795_, 0 as u32, v___x_4794_);
                lean_ctor_set_uint8(v___x_4795_, 1 as u32, v___x_4730_);
                lean_ctor_set_uint8(v___x_4795_, 2 as u32, v___x_4719_);
                lean_ctor_set_uint8(v___x_4795_, 3 as u32, v___x_4730_);
                v___x_4796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__1);
                lean_inc(v_a_4788_);
                v___x_4797_ = l_Lean_MessageData_ofConstName(v_a_4788_, v___x_4719_);
                v___x_4798_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4798_, 0, v___x_4796_);
                lean_ctor_set(v___x_4798_, 1, v___x_4797_);
                v___x_4799_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4799_, 0, v___x_4798_);
                lean_ctor_set(v___x_4799_, 1, v___x_4796_);
                if v_isShared_4793_ == 0 {
                    lean_ctor_set_tag(v___x_4792_, 1);
                    lean_ctor_set(v___x_4792_, 0, v___x_4799_);
                    v___x_4801_ = v___x_4792_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4799_);
                    v___x_4801_ = v_reuseFailAlloc_4824_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                lean_inc(v_goal_4720_);
                v___x_4802_ = l_Lean_MVarId_apply(
                    v_goal_4720_,
                    v_a_4790_,
                    v___x_4795_,
                    v___x_4801_,
                    v___y_4725_,
                    v___y_4726_,
                    v___y_4727_,
                    v___y_4728_,
                );
                if lean_obj_tag(v___x_4802_) == 0 {
                    v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
                    v_isSharedCheck_4822_ = (!lean_is_exclusive(v___x_4802_)) as u8;
                    if v_isSharedCheck_4822_ == 0 {
                        v___x_4805_ = v___x_4802_;
                        v_isShared_4806_ = v_isSharedCheck_4822_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4803_);
                        lean_dec(v___x_4802_);
                        v___x_4805_ = lean_box(0);
                        v_isShared_4806_ = v_isSharedCheck_4822_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_a_4823_ = lean_ctor_get(v___x_4802_, 0);
                    lean_inc(v_a_4823_);
                    lean_dec_ref_known(v___x_4802_, 1);
                    v_a_4785_ = v_a_4823_;
                    state = 12;
                    continue;
                }
            }
            15 => {
                v___x_4807_ = l_List_isEmpty___redArg(v_a_4803_);
                if v___x_4807_ == 0 {
                    lean_del_object(v___x_4805_);
                    v___x_4808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3;
                    v___x_4809_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5);
                    v___x_4810_ = l_Lean_Elab_goalsToMessageData(v_a_4803_);
                    v___x_4811_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4811_, 0, v___x_4809_);
                    lean_ctor_set(v___x_4811_, 1, v___x_4810_);
                    v___x_4812_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v___x_4812_, 0, v___x_4808_);
                    lean_ctor_set(v___x_4812_, 1, v___x_4811_);
                    v___x_4813_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_4812_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
                    if lean_obj_tag(v___x_4813_) == 0 {
                        lean_del_object(v___x_4734_);
                        v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
                        lean_inc(v_a_4814_);
                        lean_dec_ref_known(v___x_4813_, 1);
                        v___x_4815_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4815_, 0, v_a_4814_);
                        lean_ctor_set(v___x_4815_, 1, v_snd_4732_);
                        v_a_4738_ = v___x_4815_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4816_ = lean_ctor_get(v___x_4813_, 0);
                        lean_inc(v_a_4816_);
                        lean_dec_ref_known(v___x_4813_, 1);
                        v_a_4785_ = v_a_4816_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4803_);
                    lean_del_object(v___x_4734_);
                    lean_dec(v_goal_4720_);
                    v___x_4817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__6;
                    v___x_4818_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4818_, 0, v___x_4817_);
                    lean_ctor_set(v___x_4818_, 1, v_snd_4732_);
                    if v_isShared_4806_ == 0 {
                        lean_ctor_set(v___x_4805_, 0, v___x_4818_);
                        v___x_4820_ = v___x_4805_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4818_);
                        v___x_4820_ = v_reuseFailAlloc_4821_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_4820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___boxed(
    mut v_a_4829_: *mut LeanObject,
    mut v___x_4830_: *mut LeanObject,
    mut v_goal_4831_: *mut LeanObject,
    mut v_as_4832_: *mut LeanObject,
    mut v_sz_4833_: *mut LeanObject,
    mut v_i_4834_: *mut LeanObject,
    mut v_b_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_12797__boxed_4841_: u8 = 0;
    let mut v_sz_boxed_4842_: usize = 0;
    let mut v_i_boxed_4843_: usize = 0;
    let mut v_res_4844_: *mut LeanObject = core::ptr::null_mut();
    v___x_12797__boxed_4841_ = (lean_unbox(v___x_4830_) as u8);
    v_sz_boxed_4842_ = lean_unbox_usize(v_sz_4833_);
    lean_dec(v_sz_4833_);
    v_i_boxed_4843_ = lean_unbox_usize(v_i_4834_);
    lean_dec(v_i_4834_);
    v_res_4844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1(v_a_4829_, v___x_12797__boxed_4841_, v_goal_4831_, v_as_4832_, v_sz_boxed_4842_, v_i_boxed_4843_, v_b_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
    lean_dec(v___y_4839_);
    lean_dec_ref(v___y_4838_);
    lean_dec(v___y_4837_);
    lean_dec_ref(v___y_4836_);
    lean_dec_ref(v_as_4832_);
    lean_dec_ref(v_a_4829_);
    return v_res_4844_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__5() -> *mut LeanObject {
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4853_ = l_Lean_MVarId_applyRfl___lam__1___closed__4;
    v___x_4854_ = l_Lean_stringToMessageData(v___x_4853_);
    return v___x_4854_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__7() -> *mut LeanObject {
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    v___x_4856_ = l_Lean_MVarId_applyRfl___lam__1___closed__6;
    v___x_4857_ = l_Lean_stringToMessageData(v___x_4856_);
    return v___x_4857_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__9() -> *mut LeanObject {
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    v___x_4859_ = l_Lean_MVarId_applyRfl___lam__1___closed__8;
    v___x_4860_ = l_Lean_stringToMessageData(v___x_4859_);
    return v___x_4860_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__16() -> *mut LeanObject {
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    v___x_4875_ = l_Lean_MVarId_applyRfl___lam__1___closed__15;
    v___x_4876_ = l_Lean_stringToMessageData(v___x_4875_);
    return v___x_4876_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__18() -> *mut LeanObject {
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    v___x_4878_ = l_Lean_MVarId_applyRfl___lam__1___closed__17;
    v___x_4879_ = l_Lean_stringToMessageData(v___x_4878_);
    return v___x_4879_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__19() -> *mut LeanObject {
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    v___x_4880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__18_once),
        _init_l_Lean_MVarId_applyRfl___lam__1___closed__18,
    );
    v___x_4881_ = l_Lean_MessageData_hint_x27(v___x_4880_);
    return v___x_4881_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__20() -> *mut LeanObject {
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    v___x_4882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__19_once),
        _init_l_Lean_MVarId_applyRfl___lam__1___closed__19,
    );
    v___x_4883_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__16_once),
        _init_l_Lean_MVarId_applyRfl___lam__1___closed__16,
    );
    v___x_4884_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4884_, 0, v___x_4883_);
    lean_ctor_set(v___x_4884_, 1, v___x_4882_);
    return v___x_4884_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRfl___lam__1___closed__21() -> *mut LeanObject {
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    v___x_4885_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__20_once),
        _init_l_Lean_MVarId_applyRfl___lam__1___closed__20,
    );
    v___x_4886_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4886_, 0, v___x_4885_);
    return v___x_4886_;
}
pub unsafe fn l_Lean_MVarId_applyRfl___lam__1(
    mut v_goal_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4911_: u8 = 0;
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4925_: usize = 0;
    let mut v___x_4926_: usize = 0;
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v_fst_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v_val_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4947_: u8 = 0;
    let mut v_unused_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut v_unused_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4973_: u8 = 0;
    let mut v_a_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4977_: u8 = 0;
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_a_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4985_: u8 = 0;
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v_a_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_unused_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: u8 = 0;
    let mut v___x_5024_: u8 = 0;
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constApprox_5026_: u8 = 0;
    let mut v_isDefEqStuckEx_5027_: u8 = 0;
    let mut v_unificationHints_5028_: u8 = 0;
    let mut v_proofIrrelevance_5029_: u8 = 0;
    let mut v_assignSyntheticOpaque_5030_: u8 = 0;
    let mut v_offsetCnstrs_5031_: u8 = 0;
    let mut v_transparency_5032_: u8 = 0;
    let mut v_etaStruct_5033_: u8 = 0;
    let mut v_univApprox_5034_: u8 = 0;
    let mut v_iota_5035_: u8 = 0;
    let mut v_beta_5036_: u8 = 0;
    let mut v_proj_5037_: u8 = 0;
    let mut v_zeta_5038_: u8 = 0;
    let mut v_zetaDelta_5039_: u8 = 0;
    let mut v_zetaUnused_5040_: u8 = 0;
    let mut v_zetaHave_5041_: u8 = 0;
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5047_: u8 = 0;
    let mut v_zetaDeltaSet_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5054_: u8 = 0;
    let mut v_inTypeClassResolution_5055_: u8 = 0;
    let mut v_cacheInferType_5056_: u8 = 0;
    let mut v___x_5057_: u64 = 0;
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: u8 = 0;
    let mut v___f_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5081_: u8 = 0;
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5085_: u8 = 0;
    let mut v_reuseFailAlloc_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: u8 = 0;
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5106_: u8 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5110_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: u8 = 0;
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut v_a_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5129_: u8 = 0;
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_4887_);
                v___x_5007_ = l_Lean_MVarId_getType(
                    v_goal_4887_,
                    v___y_4888_,
                    v___y_4889_,
                    v___y_4890_,
                    v___y_4891_,
                );
                if lean_obj_tag(v___x_5007_) == 0 {
                    v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
                    lean_inc(v_a_5008_);
                    lean_dec_ref_known(v___x_5007_, 1);
                    v___x_5009_ =
                        l_Lean_instantiateMVars___at___00Lean_MVarId_applyRfl_spec__0___redArg(
                            v_a_5008_,
                            v___y_4889_,
                        );
                    v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
                    v_isSharedCheck_5125_ = (!lean_is_exclusive(v___x_5009_)) as u8;
                    if v_isSharedCheck_5125_ == 0 {
                        v___x_5012_ = v___x_5009_;
                        v_isShared_5013_ = v_isSharedCheck_5125_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5010_);
                        lean_dec(v___x_5009_);
                        v___x_5012_ = lean_box(0);
                        v_isShared_5013_ = v_isSharedCheck_5125_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec(v_goal_4887_);
                    v_a_5126_ = lean_ctor_get(v___x_5007_, 0);
                    v_isSharedCheck_5133_ = (!lean_is_exclusive(v___x_5007_)) as u8;
                    if v_isSharedCheck_5133_ == 0 {
                        v___x_5128_ = v___x_5007_;
                        v_isShared_5129_ = v_isSharedCheck_5133_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_5126_);
                        lean_dec(v___x_5007_);
                        v___x_5128_ = lean_box(0);
                        v_isShared_5129_ = v_isSharedCheck_5133_;
                        state = 29;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4894_ = lean_box(0);
                v___x_4895_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4895_, 0, v___x_4894_);
                return v___x_4895_;
            }
            2 => {
                v___x_4904_ = l_Lean_MVarId_applyRfl___lam__1___closed__0;
                v___x_4905_ = lean_unsigned_to_nat(1);
                v___x_4906_ = l_Lean_Expr_isAppOfArity(v___y_4898_, v___x_4904_, v___x_4905_);
                if v___x_4906_ == 0 {
                    v___x_4907_ = l_Lean_Expr_app___override(v___y_4899_, v___y_4897_);
                    lean_inc(v_goal_4887_);
                    v___x_4908_ =
                        l_Lean_MVarId_setType___redArg(v_goal_4887_, v___x_4907_, v___y_4901_);
                    if lean_obj_tag(v___x_4908_) == 0 {
                        v_isSharedCheck_4998_ = (!lean_is_exclusive(v___x_4908_)) as u8;
                        if v_isSharedCheck_4998_ == 0 {
                            v_unused_4999_ = lean_ctor_get(v___x_4908_, 0);
                            lean_dec(v_unused_4999_);
                            v___x_4910_ = v___x_4908_;
                            v_isShared_4911_ = v_isSharedCheck_4998_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_4908_);
                            v___x_4910_ = lean_box(0);
                            v_isShared_4911_ = v_isSharedCheck_4998_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_4898_);
                        lean_dec(v_goal_4887_);
                        return v___x_4908_;
                    }
                } else {
                    lean_dec_ref(v___y_4899_);
                    v___x_5000_ = l_Lean_Expr_appFn_x21(v___y_4898_);
                    v___x_5001_ = l_Lean_Expr_constLevels_x21(v___x_5000_);
                    lean_dec_ref(v___x_5000_);
                    v___x_5002_ = l_Lean_Expr_appArg_x21(v___y_4898_);
                    lean_dec_ref(v___y_4898_);
                    v___x_5003_ = l_Lean_MVarId_applyRfl___lam__1___closed__10;
                    v___x_5004_ = l_Lean_mkConst(v___x_5003_, v___x_5001_);
                    v___x_5005_ = l_Lean_mkAppB(v___x_5004_, v___x_5002_, v___y_4897_);
                    v___x_5006_ =
                        l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2___redArg(
                            v_goal_4887_,
                            v___x_5005_,
                            v___y_4901_,
                        );
                    return v___x_5006_;
                }
            }
            3 => {
                v___x_4912_ = l_Lean_Meta_saveState___redArg(v___y_4901_, v___y_4903_);
                if lean_obj_tag(v___x_4912_) == 0 {
                    v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
                    lean_inc(v_a_4913_);
                    lean_dec_ref_known(v___x_4912_, 1);
                    v___x_4914_ = lean_st_ref_get(v___y_4903_);
                    v_env_4915_ = lean_ctor_get(v___x_4914_, 0);
                    lean_inc_ref(v_env_4915_);
                    lean_dec(v___x_4914_);
                    v___x_4916_ = l_Lean_Meta_Rfl_reflExt;
                    v_ext_4917_ = lean_ctor_get(v___x_4916_, 1);
                    v_toEnvExtension_4918_ = lean_ctor_get(v_ext_4917_, 0);
                    v_asyncMode_4919_ = lean_ctor_get(v_toEnvExtension_4918_, 2);
                    v___x_4920_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0);
                    v___x_4921_ = l_Lean_ScopedEnvExtension_getState___redArg(
                        v___x_4920_,
                        v___x_4916_,
                        v_env_4915_,
                        v_asyncMode_4919_,
                    );
                    lean_inc_ref(v___y_4898_);
                    v___x_4922_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
                        v___x_4921_,
                        v___y_4898_,
                        v___y_4900_,
                        v___y_4901_,
                        v___y_4902_,
                        v___y_4903_,
                    );
                    lean_dec(v___x_4921_);
                    if lean_obj_tag(v___x_4922_) == 0 {
                        v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
                        lean_inc(v_a_4923_);
                        lean_dec_ref_known(v___x_4922_, 1);
                        v___x_4924_ = l_Lean_MVarId_applyRfl___lam__1___closed__1;
                        v_sz_4925_ = lean_array_size(v_a_4923_);
                        v___x_4926_ = 0usize;
                        lean_inc(v_goal_4887_);
                        v___x_4927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1(v_a_4913_, v___x_4906_, v_goal_4887_, v_a_4923_, v_sz_4925_, v___x_4926_, v___x_4924_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_);
                        lean_dec(v_a_4923_);
                        lean_dec(v_a_4913_);
                        if lean_obj_tag(v___x_4927_) == 0 {
                            v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
                            v_isSharedCheck_4973_ = (!lean_is_exclusive(v___x_4927_)) as u8;
                            if v_isSharedCheck_4973_ == 0 {
                                v___x_4930_ = v___x_4927_;
                                v_isShared_4931_ = v_isSharedCheck_4973_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4928_);
                                lean_dec(v___x_4927_);
                                v___x_4930_ = lean_box(0);
                                v_isShared_4931_ = v_isSharedCheck_4973_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4910_);
                            lean_dec_ref(v___y_4898_);
                            lean_dec(v_goal_4887_);
                            v_a_4974_ = lean_ctor_get(v___x_4927_, 0);
                            v_isSharedCheck_4981_ = (!lean_is_exclusive(v___x_4927_)) as u8;
                            if v_isSharedCheck_4981_ == 0 {
                                v___x_4976_ = v___x_4927_;
                                v_isShared_4977_ = v_isSharedCheck_4981_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_4974_);
                                lean_dec(v___x_4927_);
                                v___x_4976_ = lean_box(0);
                                v_isShared_4977_ = v_isSharedCheck_4981_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4913_);
                        lean_del_object(v___x_4910_);
                        lean_dec_ref(v___y_4898_);
                        lean_dec(v_goal_4887_);
                        v_a_4982_ = lean_ctor_get(v___x_4922_, 0);
                        v_isSharedCheck_4989_ = (!lean_is_exclusive(v___x_4922_)) as u8;
                        if v_isSharedCheck_4989_ == 0 {
                            v___x_4984_ = v___x_4922_;
                            v_isShared_4985_ = v_isSharedCheck_4989_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4982_);
                            lean_dec(v___x_4922_);
                            v___x_4984_ = lean_box(0);
                            v_isShared_4985_ = v_isSharedCheck_4989_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4910_);
                    lean_dec_ref(v___y_4898_);
                    lean_dec(v_goal_4887_);
                    v_a_4990_ = lean_ctor_get(v___x_4912_, 0);
                    v_isSharedCheck_4997_ = (!lean_is_exclusive(v___x_4912_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4992_ = v___x_4912_;
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4990_);
                        lean_dec(v___x_4912_);
                        v___x_4992_ = lean_box(0);
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 15;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_4932_ = lean_ctor_get(v_a_4928_, 0);
                if lean_obj_tag(v_fst_4932_) == 0 {
                    lean_del_object(v___x_4930_);
                    v_snd_4933_ = lean_ctor_get(v_a_4928_, 1);
                    v_isSharedCheck_4967_ = (!lean_is_exclusive(v_a_4928_)) as u8;
                    if v_isSharedCheck_4967_ == 0 {
                        v_unused_4968_ = lean_ctor_get(v_a_4928_, 0);
                        lean_dec(v_unused_4968_);
                        v___x_4935_ = v_a_4928_;
                        v_isShared_4936_ = v_isSharedCheck_4967_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_4933_);
                        lean_dec(v_a_4928_);
                        v___x_4935_ = lean_box(0);
                        v_isShared_4936_ = v_isSharedCheck_4967_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4932_);
                    lean_dec(v_a_4928_);
                    lean_del_object(v___x_4910_);
                    lean_dec_ref(v___y_4898_);
                    lean_dec(v_goal_4887_);
                    v_val_4969_ = lean_ctor_get(v_fst_4932_, 0);
                    lean_inc(v_val_4969_);
                    lean_dec_ref_known(v_fst_4932_, 1);
                    if v_isShared_4931_ == 0 {
                        lean_ctor_set(v___x_4930_, 0, v_val_4969_);
                        v___x_4971_ = v___x_4930_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_val_4969_);
                        v___x_4971_ = v_reuseFailAlloc_4972_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_snd_4933_) == 1 {
                    lean_del_object(v___x_4935_);
                    lean_del_object(v___x_4910_);
                    lean_dec_ref(v___y_4898_);
                    lean_dec(v_goal_4887_);
                    v_val_4937_ = lean_ctor_get(v_snd_4933_, 0);
                    lean_inc(v_val_4937_);
                    lean_dec_ref_known(v_snd_4933_, 1);
                    v_fst_4938_ = lean_ctor_get(v_val_4937_, 0);
                    lean_inc(v_fst_4938_);
                    v_snd_4939_ = lean_ctor_get(v_val_4937_, 1);
                    lean_inc(v_snd_4939_);
                    lean_dec(v_val_4937_);
                    v___x_4940_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_fst_4938_,
                        v___y_4901_,
                        v___y_4903_,
                    );
                    lean_dec(v_fst_4938_);
                    if lean_obj_tag(v___x_4940_) == 0 {
                        v_isSharedCheck_4947_ = (!lean_is_exclusive(v___x_4940_)) as u8;
                        if v_isSharedCheck_4947_ == 0 {
                            v_unused_4948_ = lean_ctor_get(v___x_4940_, 0);
                            lean_dec(v_unused_4948_);
                            v___x_4942_ = v___x_4940_;
                            v_isShared_4943_ = v_isSharedCheck_4947_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_4940_);
                            v___x_4942_ = lean_box(0);
                            v_isShared_4943_ = v_isSharedCheck_4947_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4939_);
                        return v___x_4940_;
                    }
                } else {
                    lean_dec(v_snd_4933_);
                    v___x_4949_ = l_Lean_MVarId_applyRfl___lam__1___closed__3;
                    v___x_4950_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__5_once),
                        _init_l_Lean_MVarId_applyRfl___lam__1___closed__5,
                    );
                    lean_inc_ref(v___y_4898_);
                    v___x_4951_ = l_Lean_indentExpr(v___y_4898_);
                    if v_isShared_4936_ == 0 {
                        lean_ctor_set_tag(v___x_4935_, 7);
                        lean_ctor_set(v___x_4935_, 1, v___x_4951_);
                        lean_ctor_set(v___x_4935_, 0, v___x_4950_);
                        v___x_4953_ = v___x_4935_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4966_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4950_);
                        lean_ctor_set(v_reuseFailAlloc_4966_, 1, v___x_4951_);
                        v___x_4953_ = v_reuseFailAlloc_4966_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4943_ == 0 {
                    lean_ctor_set_tag(v___x_4942_, 1);
                    lean_ctor_set(v___x_4942_, 0, v_snd_4939_);
                    v___x_4945_ = v___x_4942_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_snd_4939_);
                    v___x_4945_ = v_reuseFailAlloc_4946_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4945_;
            }
            8 => {
                v___x_4954_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__7_once),
                    _init_l_Lean_MVarId_applyRfl___lam__1___closed__7,
                );
                v___x_4955_ = lean_unsigned_to_nat(30);
                v___x_4956_ = l_Lean_inlineExpr(v___y_4898_, v___x_4955_);
                v___x_4957_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4957_, 0, v___x_4954_);
                lean_ctor_set(v___x_4957_, 1, v___x_4956_);
                v___x_4958_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__9_once),
                    _init_l_Lean_MVarId_applyRfl___lam__1___closed__9,
                );
                v___x_4959_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4959_, 0, v___x_4957_);
                lean_ctor_set(v___x_4959_, 1, v___x_4958_);
                v___x_4960_ = l_Lean_MessageData_hint_x27(v___x_4959_);
                v___x_4961_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4961_, 0, v___x_4953_);
                lean_ctor_set(v___x_4961_, 1, v___x_4960_);
                if v_isShared_4911_ == 0 {
                    lean_ctor_set_tag(v___x_4910_, 1);
                    lean_ctor_set(v___x_4910_, 0, v___x_4961_);
                    v___x_4963_ = v___x_4910_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4961_);
                    v___x_4963_ = v_reuseFailAlloc_4965_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4964_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_4949_,
                    v_goal_4887_,
                    v___x_4963_,
                    v___y_4900_,
                    v___y_4901_,
                    v___y_4902_,
                    v___y_4903_,
                );
                return v___x_4964_;
            }
            10 => {
                return v___x_4971_;
            }
            11 => {
                if v_isShared_4977_ == 0 {
                    v___x_4979_ = v___x_4976_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4974_);
                    v___x_4979_ = v_reuseFailAlloc_4980_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4979_;
            }
            13 => {
                if v_isShared_4985_ == 0 {
                    v___x_4987_ = v___x_4984_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
                    v___x_4987_ = v_reuseFailAlloc_4988_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4987_;
            }
            15 => {
                if v_isShared_4993_ == 0 {
                    v___x_4995_ = v___x_4992_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4995_;
            }
            17 => {
                v___x_5014_ = l_Lean_Meta_whnfR(
                    v_a_5010_,
                    v___y_4888_,
                    v___y_4889_,
                    v___y_4890_,
                    v___y_4891_,
                );
                if lean_obj_tag(v___x_5014_) == 0 {
                    v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
                    lean_inc(v_a_5015_);
                    lean_dec_ref_known(v___x_5014_, 1);
                    v___x_5111_ = l_Lean_Expr_getAppNumArgs(v_a_5015_);
                    v___x_5112_ = lean_unsigned_to_nat(2);
                    v___x_5113_ = lean_nat_dec_lt(v___x_5111_, v___x_5112_);
                    lean_dec(v___x_5111_);
                    if v___x_5113_ == 0 {
                        v___y_5017_ = v___y_4888_;
                        v___y_5018_ = v___y_4889_;
                        v___y_5019_ = v___y_4890_;
                        v___y_5020_ = v___y_4891_;
                        state = 18;
                        continue;
                    } else {
                        v___x_5114_ = l_Lean_MVarId_applyRfl___lam__1___closed__3;
                        v___x_5115_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_applyRfl___lam__1___closed__21),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_applyRfl___lam__1___closed__21_once
                            ),
                            _init_l_Lean_MVarId_applyRfl___lam__1___closed__21,
                        );
                        lean_inc(v_goal_4887_);
                        v___x_5116_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_5114_,
                            v_goal_4887_,
                            v___x_5115_,
                            v___y_4888_,
                            v___y_4889_,
                            v___y_4890_,
                            v___y_4891_,
                        );
                        if lean_obj_tag(v___x_5116_) == 0 {
                            lean_dec_ref_known(v___x_5116_, 1);
                            v___y_5017_ = v___y_4888_;
                            v___y_5018_ = v___y_4889_;
                            v___y_5019_ = v___y_4890_;
                            v___y_5020_ = v___y_4891_;
                            state = 18;
                            continue;
                        } else {
                            lean_dec(v_a_5015_);
                            lean_del_object(v___x_5012_);
                            lean_dec(v_goal_4887_);
                            return v___x_5116_;
                        }
                    }
                } else {
                    lean_del_object(v___x_5012_);
                    lean_dec(v_goal_4887_);
                    v_a_5117_ = lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5124_ = (!lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5124_ == 0 {
                        v___x_5119_ = v___x_5014_;
                        v_isShared_5120_ = v_isSharedCheck_5124_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_5117_);
                        lean_dec(v___x_5014_);
                        v___x_5119_ = lean_box(0);
                        v_isShared_5120_ = v_isSharedCheck_5124_;
                        state = 27;
                        continue;
                    }
                }
            }
            18 => {
                v___x_5021_ = l_Lean_MVarId_applyRfl___lam__1___closed__12;
                v___x_5022_ = lean_unsigned_to_nat(4);
                v___x_5023_ = l_Lean_Expr_isAppOfArity(v_a_5015_, v___x_5021_, v___x_5022_);
                v___x_5024_ = 1;
                if v___x_5023_ == 0 {
                    v___x_5025_ = l_Lean_Meta_Context_config(v___y_5017_);
                    v_constApprox_5026_ = lean_ctor_get_uint8(v___x_5025_, 3 as u32);
                    v_isDefEqStuckEx_5027_ = lean_ctor_get_uint8(v___x_5025_, 4 as u32);
                    v_unificationHints_5028_ = lean_ctor_get_uint8(v___x_5025_, 5 as u32);
                    v_proofIrrelevance_5029_ = lean_ctor_get_uint8(v___x_5025_, 6 as u32);
                    v_assignSyntheticOpaque_5030_ = lean_ctor_get_uint8(v___x_5025_, 7 as u32);
                    v_offsetCnstrs_5031_ = lean_ctor_get_uint8(v___x_5025_, 8 as u32);
                    v_transparency_5032_ = lean_ctor_get_uint8(v___x_5025_, 9 as u32);
                    v_etaStruct_5033_ = lean_ctor_get_uint8(v___x_5025_, 10 as u32);
                    v_univApprox_5034_ = lean_ctor_get_uint8(v___x_5025_, 11 as u32);
                    v_iota_5035_ = lean_ctor_get_uint8(v___x_5025_, 12 as u32);
                    v_beta_5036_ = lean_ctor_get_uint8(v___x_5025_, 13 as u32);
                    v_proj_5037_ = lean_ctor_get_uint8(v___x_5025_, 14 as u32);
                    v_zeta_5038_ = lean_ctor_get_uint8(v___x_5025_, 15 as u32);
                    v_zetaDelta_5039_ = lean_ctor_get_uint8(v___x_5025_, 16 as u32);
                    v_zetaUnused_5040_ = lean_ctor_get_uint8(v___x_5025_, 17 as u32);
                    v_zetaHave_5041_ = lean_ctor_get_uint8(v___x_5025_, 18 as u32);
                    v_isSharedCheck_5087_ = (!lean_is_exclusive(v___x_5025_)) as u8;
                    if v_isSharedCheck_5087_ == 0 {
                        v___x_5043_ = v___x_5025_;
                        v_isShared_5044_ = v_isSharedCheck_5087_;
                        state = 19;
                        continue;
                    } else {
                        lean_dec(v___x_5025_);
                        v___x_5043_ = lean_box(0);
                        v_isShared_5044_ = v_isSharedCheck_5087_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5015_);
                    v___x_5088_ = l_Lean_MVarId_applyRfl___lam__1___closed__13;
                    v___x_5089_ = l_Lean_MVarId_applyRfl___lam__1___closed__14;
                    lean_inc(v_goal_4887_);
                    v___x_5090_ = l_Lean_MVarId_applyConst(
                        v_goal_4887_,
                        v___x_5088_,
                        v___x_5089_,
                        v___y_5017_,
                        v___y_5018_,
                        v___y_5019_,
                        v___y_5020_,
                    );
                    if lean_obj_tag(v___x_5090_) == 0 {
                        v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
                        lean_inc(v_a_5091_);
                        lean_dec_ref_known(v___x_5090_, 1);
                        v___x_5092_ = l_List_isEmpty___redArg(v_a_5091_);
                        if v___x_5092_ == 0 {
                            v___x_5093_ = l_Lean_MVarId_applyRfl___lam__1___closed__3;
                            v___x_5094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__3;
                            v___x_5095_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_applyRfl_spec__1___closed__5);
                            v___x_5096_ = l_Lean_Elab_goalsToMessageData(v_a_5091_);
                            v___x_5097_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5097_, 0, v___x_5095_);
                            lean_ctor_set(v___x_5097_, 1, v___x_5096_);
                            v___x_5098_ = lean_alloc_ctor(8, 2, (0) as u32);
                            lean_ctor_set(v___x_5098_, 0, v___x_5094_);
                            lean_ctor_set(v___x_5098_, 1, v___x_5097_);
                            if v_isShared_5013_ == 0 {
                                lean_ctor_set_tag(v___x_5012_, 1);
                                lean_ctor_set(v___x_5012_, 0, v___x_5098_);
                                v___x_5100_ = v___x_5012_;
                                state = 24;
                                continue;
                            } else {
                                v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5098_);
                                v___x_5100_ = v_reuseFailAlloc_5102_;
                                state = 24;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5091_);
                            lean_del_object(v___x_5012_);
                            lean_dec(v_goal_4887_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5012_);
                        lean_dec(v_goal_4887_);
                        v_a_5103_ = lean_ctor_get(v___x_5090_, 0);
                        v_isSharedCheck_5110_ = (!lean_is_exclusive(v___x_5090_)) as u8;
                        if v_isSharedCheck_5110_ == 0 {
                            v___x_5105_ = v___x_5090_;
                            v_isShared_5106_ = v_isSharedCheck_5110_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_5103_);
                            lean_dec(v___x_5090_);
                            v___x_5105_ = lean_box(0);
                            v_isShared_5106_ = v_isSharedCheck_5110_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_5044_ == 0 {
                    v___x_5046_ = v___x_5043_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 3 as u32, v_constApprox_5026_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 4 as u32, v_isDefEqStuckEx_5027_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 5 as u32, v_unificationHints_5028_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 6 as u32, v_proofIrrelevance_5029_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5086_,
                        7 as u32,
                        v_assignSyntheticOpaque_5030_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 8 as u32, v_offsetCnstrs_5031_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 9 as u32, v_transparency_5032_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 10 as u32, v_etaStruct_5033_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 11 as u32, v_univApprox_5034_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 12 as u32, v_iota_5035_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 13 as u32, v_beta_5036_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 14 as u32, v_proj_5037_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 15 as u32, v_zeta_5038_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 16 as u32, v_zetaDelta_5039_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 17 as u32, v_zetaUnused_5040_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5086_, 18 as u32, v_zetaHave_5041_);
                    v___x_5046_ = v_reuseFailAlloc_5086_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                lean_ctor_set_uint8(v___x_5046_, 0 as u32, v___x_5024_);
                lean_ctor_set_uint8(v___x_5046_, 1 as u32, v___x_5024_);
                lean_ctor_set_uint8(v___x_5046_, 2 as u32, v___x_5024_);
                v_trackZetaDelta_5047_ = lean_ctor_get_uint8(
                    v___y_5017_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5048_ = lean_ctor_get(v___y_5017_, 1);
                v_lctx_5049_ = lean_ctor_get(v___y_5017_, 2);
                v_localInstances_5050_ = lean_ctor_get(v___y_5017_, 3);
                v_defEqCtx_x3f_5051_ = lean_ctor_get(v___y_5017_, 4);
                v_synthPendingDepth_5052_ = lean_ctor_get(v___y_5017_, 5);
                v_canUnfold_x3f_5053_ = lean_ctor_get(v___y_5017_, 6);
                v_univApprox_5054_ = lean_ctor_get_uint8(
                    v___y_5017_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5055_ = lean_ctor_get_uint8(
                    v___y_5017_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5056_ = lean_ctor_get_uint8(
                    v___y_5017_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_5057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5046_);
                v___x_5058_ = l_Lean_Expr_appFn_x21(v_a_5015_);
                v___x_5059_ = l_Lean_Expr_appArg_x21(v___x_5058_);
                v___x_5060_ = l_Lean_Expr_appArg_x21(v_a_5015_);
                lean_dec(v_a_5015_);
                v___x_5061_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5061_, 0, v___x_5046_);
                lean_ctor_set_uint64(
                    v___x_5061_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5057_,
                );
                lean_inc(v_canUnfold_x3f_5053_);
                lean_inc(v_synthPendingDepth_5052_);
                lean_inc(v_defEqCtx_x3f_5051_);
                lean_inc_ref(v_localInstances_5050_);
                lean_inc_ref(v_lctx_5049_);
                lean_inc(v_zetaDeltaSet_5048_);
                v___x_5062_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5062_, 0, v___x_5061_);
                lean_ctor_set(v___x_5062_, 1, v_zetaDeltaSet_5048_);
                lean_ctor_set(v___x_5062_, 2, v_lctx_5049_);
                lean_ctor_set(v___x_5062_, 3, v_localInstances_5050_);
                lean_ctor_set(v___x_5062_, 4, v_defEqCtx_x3f_5051_);
                lean_ctor_set(v___x_5062_, 5, v_synthPendingDepth_5052_);
                lean_ctor_set(v___x_5062_, 6, v_canUnfold_x3f_5053_);
                lean_ctor_set_uint8(
                    v___x_5062_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5047_,
                );
                lean_ctor_set_uint8(
                    v___x_5062_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5054_,
                );
                lean_ctor_set_uint8(
                    v___x_5062_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5055_,
                );
                lean_ctor_set_uint8(
                    v___x_5062_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5056_,
                );
                lean_inc_ref(v___x_5060_);
                lean_inc_ref(v___x_5059_);
                v___x_5063_ = l_Lean_Meta_isExprDefEqGuarded(
                    v___x_5059_,
                    v___x_5060_,
                    v___x_5062_,
                    v___y_5018_,
                    v___y_5019_,
                    v___y_5020_,
                );
                lean_dec_ref_known(v___x_5062_, 7);
                if lean_obj_tag(v___x_5063_) == 0 {
                    v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
                    lean_inc(v_a_5064_);
                    lean_dec_ref_known(v___x_5063_, 1);
                    v___x_5065_ = l_Lean_Expr_appFn_x21(v___x_5058_);
                    v___x_5066_ = (lean_unbox(v_a_5064_) as u8);
                    lean_dec(v_a_5064_);
                    if v___x_5066_ == 0 {
                        lean_inc_ref(v___x_5060_);
                        lean_inc_ref_n(v___x_5059_, 2);
                        v___f_5067_ = lean_alloc_closure(
                            l_Lean_MVarId_applyRfl___lam__0___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___f_5067_, 0, v___x_5059_);
                        lean_closure_set(v___f_5067_, 1, v___x_5060_);
                        v___x_5068_ = lean_unsigned_to_nat(2);
                        v___x_5069_ = lean_mk_empty_array_with_capacity(v___x_5068_);
                        v___x_5070_ = lean_array_push(v___x_5069_, v___x_5059_);
                        v___x_5071_ = lean_array_push(v___x_5070_, v___x_5060_);
                        v___x_5072_ = l_Lean_MessageData_ofLazyM(v___f_5067_, v___x_5071_);
                        v___x_5073_ = l_Lean_MVarId_applyRfl___lam__1___closed__3;
                        if v_isShared_5013_ == 0 {
                            lean_ctor_set_tag(v___x_5012_, 1);
                            lean_ctor_set(v___x_5012_, 0, v___x_5072_);
                            v___x_5075_ = v___x_5012_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5072_);
                            v___x_5075_ = v_reuseFailAlloc_5077_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_5060_);
                        lean_del_object(v___x_5012_);
                        v___y_4897_ = v___x_5059_;
                        v___y_4898_ = v___x_5065_;
                        v___y_4899_ = v___x_5058_;
                        v___y_4900_ = v___y_5017_;
                        v___y_4901_ = v___y_5018_;
                        v___y_4902_ = v___y_5019_;
                        v___y_4903_ = v___y_5020_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5060_);
                    lean_dec_ref(v___x_5059_);
                    lean_dec_ref(v___x_5058_);
                    lean_del_object(v___x_5012_);
                    lean_dec(v_goal_4887_);
                    v_a_5078_ = lean_ctor_get(v___x_5063_, 0);
                    v_isSharedCheck_5085_ = (!lean_is_exclusive(v___x_5063_)) as u8;
                    if v_isSharedCheck_5085_ == 0 {
                        v___x_5080_ = v___x_5063_;
                        v_isShared_5081_ = v_isSharedCheck_5085_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_5078_);
                        lean_dec(v___x_5063_);
                        v___x_5080_ = lean_box(0);
                        v_isShared_5081_ = v_isSharedCheck_5085_;
                        state = 22;
                        continue;
                    }
                }
            }
            21 => {
                lean_inc(v_goal_4887_);
                v___x_5076_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5073_,
                    v_goal_4887_,
                    v___x_5075_,
                    v___y_5017_,
                    v___y_5018_,
                    v___y_5019_,
                    v___y_5020_,
                );
                if lean_obj_tag(v___x_5076_) == 0 {
                    lean_dec_ref_known(v___x_5076_, 1);
                    v___y_4897_ = v___x_5059_;
                    v___y_4898_ = v___x_5065_;
                    v___y_4899_ = v___x_5058_;
                    v___y_4900_ = v___y_5017_;
                    v___y_4901_ = v___y_5018_;
                    v___y_4902_ = v___y_5019_;
                    v___y_4903_ = v___y_5020_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___x_5065_);
                    lean_dec_ref(v___x_5059_);
                    lean_dec_ref(v___x_5058_);
                    lean_dec(v_goal_4887_);
                    return v___x_5076_;
                }
            }
            22 => {
                if v_isShared_5081_ == 0 {
                    v___x_5083_ = v___x_5080_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
                    v___x_5083_ = v_reuseFailAlloc_5084_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5083_;
            }
            24 => {
                v___x_5101_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5093_,
                    v_goal_4887_,
                    v___x_5100_,
                    v___y_5017_,
                    v___y_5018_,
                    v___y_5019_,
                    v___y_5020_,
                );
                if lean_obj_tag(v___x_5101_) == 0 {
                    lean_dec_ref_known(v___x_5101_, 1);
                    state = 1;
                    continue;
                } else {
                    return v___x_5101_;
                }
            }
            25 => {
                if v_isShared_5106_ == 0 {
                    v___x_5108_ = v___x_5105_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
                    v___x_5108_ = v_reuseFailAlloc_5109_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5108_;
            }
            27 => {
                if v_isShared_5120_ == 0 {
                    v___x_5122_ = v___x_5119_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
                    v___x_5122_ = v_reuseFailAlloc_5123_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5122_;
            }
            29 => {
                if v_isShared_5129_ == 0 {
                    v___x_5131_ = v___x_5128_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
                    v___x_5131_ = v_reuseFailAlloc_5132_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyRfl___lam__1___boxed(
    mut v_goal_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
    mut v___y_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5140_: *mut LeanObject = core::ptr::null_mut();
    v_res_5140_ = l_Lean_MVarId_applyRfl___lam__1(
        v_goal_5134_,
        v___y_5135_,
        v___y_5136_,
        v___y_5137_,
        v___y_5138_,
    );
    lean_dec(v___y_5138_);
    lean_dec_ref(v___y_5137_);
    lean_dec(v___y_5136_);
    lean_dec_ref(v___y_5135_);
    return v_res_5140_;
}
pub unsafe fn l_Lean_MVarId_applyRfl(
    mut v_goal_5141_: *mut LeanObject,
    mut v_a_5142_: *mut LeanObject,
    mut v_a_5143_: *mut LeanObject,
    mut v_a_5144_: *mut LeanObject,
    mut v_a_5145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_5141_);
    v___f_5147_ = lean_alloc_closure(
        l_Lean_MVarId_applyRfl___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5147_, 0, v_goal_5141_);
    v___x_5148_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_applyRfl_spec__3___redArg(
        v_goal_5141_,
        v___f_5147_,
        v_a_5142_,
        v_a_5143_,
        v_a_5144_,
        v_a_5145_,
    );
    return v___x_5148_;
}
pub unsafe fn l_Lean_MVarId_applyRfl___boxed(
    mut v_goal_5149_: *mut LeanObject,
    mut v_a_5150_: *mut LeanObject,
    mut v_a_5151_: *mut LeanObject,
    mut v_a_5152_: *mut LeanObject,
    mut v_a_5153_: *mut LeanObject,
    mut v_a_5154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5155_: *mut LeanObject = core::ptr::null_mut();
    v_res_5155_ = l_Lean_MVarId_applyRfl(v_goal_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_);
    lean_dec(v_a_5153_);
    lean_dec_ref(v_a_5152_);
    lean_dec(v_a_5151_);
    lean_dec_ref(v_a_5150_);
    return v_res_5155_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2(
    mut v_mvarId_5156_: *mut LeanObject,
    mut v_val_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    v___x_5163_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2___redArg(
        v_mvarId_5156_,
        v_val_5157_,
        v___y_5159_,
    );
    return v___x_5163_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2___boxed(
    mut v_mvarId_5164_: *mut LeanObject,
    mut v_val_5165_: *mut LeanObject,
    mut v___y_5166_: *mut LeanObject,
    mut v___y_5167_: *mut LeanObject,
    mut v___y_5168_: *mut LeanObject,
    mut v___y_5169_: *mut LeanObject,
    mut v___y_5170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5171_: *mut LeanObject = core::ptr::null_mut();
    v_res_5171_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2(
        v_mvarId_5164_,
        v_val_5165_,
        v___y_5166_,
        v___y_5167_,
        v___y_5168_,
        v___y_5169_,
    );
    lean_dec(v___y_5169_);
    lean_dec_ref(v___y_5168_);
    lean_dec(v___y_5167_);
    lean_dec_ref(v___y_5166_);
    return v_res_5171_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2(
    mut v_00_u03b2_5172_: *mut LeanObject,
    mut v_x_5173_: *mut LeanObject,
    mut v_x_5174_: *mut LeanObject,
    mut v_x_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    v___x_5176_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2___redArg(v_x_5173_, v_x_5174_, v_x_5175_);
    return v___x_5176_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4(
    mut v_00_u03b2_5177_: *mut LeanObject,
    mut v_x_5178_: *mut LeanObject,
    mut v_x_5179_: usize,
    mut v_x_5180_: usize,
    mut v_x_5181_: *mut LeanObject,
    mut v_x_5182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    v___x_5183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___redArg(v_x_5178_, v_x_5179_, v_x_5180_, v_x_5181_, v_x_5182_);
    return v___x_5183_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_5184_: *mut LeanObject,
    mut v_x_5185_: *mut LeanObject,
    mut v_x_5186_: *mut LeanObject,
    mut v_x_5187_: *mut LeanObject,
    mut v_x_5188_: *mut LeanObject,
    mut v_x_5189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13648__boxed_5190_: usize = 0;
    let mut v_x_13649__boxed_5191_: usize = 0;
    let mut v_res_5192_: *mut LeanObject = core::ptr::null_mut();
    v_x_13648__boxed_5190_ = lean_unbox_usize(v_x_5186_);
    lean_dec(v_x_5186_);
    v_x_13649__boxed_5191_ = lean_unbox_usize(v_x_5187_);
    lean_dec(v_x_5187_);
    v_res_5192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4(v_00_u03b2_5184_, v_x_5185_, v_x_13648__boxed_5190_, v_x_13649__boxed_5191_, v_x_5188_, v_x_5189_);
    return v_res_5192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5(
    mut v_00_u03b2_5193_: *mut LeanObject,
    mut v_n_5194_: *mut LeanObject,
    mut v_k_5195_: *mut LeanObject,
    mut v_v_5196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5___redArg(v_n_5194_, v_k_5195_, v_v_5196_);
    return v___x_5197_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6(
    mut v_00_u03b2_5198_: *mut LeanObject,
    mut v_depth_5199_: usize,
    mut v_keys_5200_: *mut LeanObject,
    mut v_vals_5201_: *mut LeanObject,
    mut v_heq_5202_: *mut LeanObject,
    mut v_i_5203_: *mut LeanObject,
    mut v_entries_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    v___x_5205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_5199_, v_keys_5200_, v_vals_5201_, v_i_5203_, v_entries_5204_);
    return v___x_5205_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_5206_: *mut LeanObject,
    mut v_depth_5207_: *mut LeanObject,
    mut v_keys_5208_: *mut LeanObject,
    mut v_vals_5209_: *mut LeanObject,
    mut v_heq_5210_: *mut LeanObject,
    mut v_i_5211_: *mut LeanObject,
    mut v_entries_5212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5213_: usize = 0;
    let mut v_res_5214_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5213_ = lean_unbox_usize(v_depth_5207_);
    lean_dec(v_depth_5207_);
    v_res_5214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_5206_, v_depth_boxed_5213_, v_keys_5208_, v_vals_5209_, v_heq_5210_, v_i_5211_, v_entries_5212_);
    lean_dec_ref(v_vals_5209_);
    lean_dec_ref(v_keys_5208_);
    return v_res_5214_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_5215_: *mut LeanObject,
    mut v_x_5216_: *mut LeanObject,
    mut v_x_5217_: *mut LeanObject,
    mut v_x_5218_: *mut LeanObject,
    mut v_x_5219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    v___x_5220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_applyRfl_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_x_5216_, v_x_5217_, v_x_5218_, v_x_5219_);
    return v___x_5220_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0___redArg(
    mut v_x_5221_: *mut LeanObject,
    mut v___y_5222_: *mut LeanObject,
    mut v___y_5223_: *mut LeanObject,
    mut v___y_5224_: *mut LeanObject,
    mut v___y_5225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5233_: u8 = 0;
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5238_: u8 = 0;
    let mut v_a_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v___y_5244_: u8 = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5248_: u8 = 0;
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v_unused_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: u8 = 0;
    let mut v___x_5267_: u8 = 0;
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v_a_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5272_: u8 = 0;
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5227_ = l_Lean_Meta_saveState___redArg(v___y_5223_, v___y_5225_);
                if lean_obj_tag(v___x_5227_) == 0 {
                    v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
                    lean_inc(v_a_5228_);
                    lean_dec_ref_known(v___x_5227_, 1);
                    lean_inc(v___y_5225_);
                    lean_inc_ref(v___y_5224_);
                    lean_inc(v___y_5223_);
                    lean_inc_ref(v___y_5222_);
                    v___x_5229_ = lean_apply_5(
                        v_x_5221_,
                        v___y_5222_,
                        v___y_5223_,
                        v___y_5224_,
                        v___y_5225_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5229_) == 0 {
                        lean_dec(v_a_5228_);
                        v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
                        v_isSharedCheck_5238_ = (!lean_is_exclusive(v___x_5229_)) as u8;
                        if v_isSharedCheck_5238_ == 0 {
                            v___x_5232_ = v___x_5229_;
                            v_isShared_5233_ = v_isSharedCheck_5238_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5230_);
                            lean_dec(v___x_5229_);
                            v___x_5232_ = lean_box(0);
                            v_isShared_5233_ = v_isSharedCheck_5238_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5239_ = lean_ctor_get(v___x_5229_, 0);
                        v_isSharedCheck_5268_ = (!lean_is_exclusive(v___x_5229_)) as u8;
                        if v_isSharedCheck_5268_ == 0 {
                            v___x_5241_ = v___x_5229_;
                            v_isShared_5242_ = v_isSharedCheck_5268_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5239_);
                            lean_dec(v___x_5229_);
                            v___x_5241_ = lean_box(0);
                            v_isShared_5242_ = v_isSharedCheck_5268_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_5221_);
                    v_a_5269_ = lean_ctor_get(v___x_5227_, 0);
                    v_isSharedCheck_5276_ = (!lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5276_ == 0 {
                        v___x_5271_ = v___x_5227_;
                        v_isShared_5272_ = v_isSharedCheck_5276_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5269_);
                        lean_dec(v___x_5227_);
                        v___x_5271_ = lean_box(0);
                        v_isShared_5272_ = v_isSharedCheck_5276_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5234_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5234_, 0, v_a_5230_);
                if v_isShared_5233_ == 0 {
                    lean_ctor_set(v___x_5232_, 0, v___x_5234_);
                    v___x_5236_ = v___x_5232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5234_);
                    v___x_5236_ = v_reuseFailAlloc_5237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5236_;
            }
            3 => {
                v___x_5266_ = l_Lean_Exception_isInterrupt(v_a_5239_);
                if v___x_5266_ == 0 {
                    lean_inc(v_a_5239_);
                    v___x_5267_ = l_Lean_Exception_isRuntime(v_a_5239_);
                    v___y_5244_ = v___x_5267_;
                    state = 4;
                    continue;
                } else {
                    v___y_5244_ = v___x_5266_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_5244_ == 0 {
                    lean_del_object(v___x_5241_);
                    lean_dec(v_a_5239_);
                    v___x_5245_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_5228_,
                        v___y_5223_,
                        v___y_5225_,
                    );
                    lean_dec(v_a_5228_);
                    if lean_obj_tag(v___x_5245_) == 0 {
                        v_isSharedCheck_5253_ = (!lean_is_exclusive(v___x_5245_)) as u8;
                        if v_isSharedCheck_5253_ == 0 {
                            v_unused_5254_ = lean_ctor_get(v___x_5245_, 0);
                            lean_dec(v_unused_5254_);
                            v___x_5247_ = v___x_5245_;
                            v_isShared_5248_ = v_isSharedCheck_5253_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_5245_);
                            v___x_5247_ = lean_box(0);
                            v_isShared_5248_ = v_isSharedCheck_5253_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_5255_ = lean_ctor_get(v___x_5245_, 0);
                        v_isSharedCheck_5262_ = (!lean_is_exclusive(v___x_5245_)) as u8;
                        if v_isSharedCheck_5262_ == 0 {
                            v___x_5257_ = v___x_5245_;
                            v_isShared_5258_ = v_isSharedCheck_5262_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5255_);
                            lean_dec(v___x_5245_);
                            v___x_5257_ = lean_box(0);
                            v_isShared_5258_ = v_isSharedCheck_5262_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5228_);
                    if v_isShared_5242_ == 0 {
                        v___x_5264_ = v___x_5241_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5239_);
                        v___x_5264_ = v_reuseFailAlloc_5265_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5249_ = lean_box(0);
                if v_isShared_5248_ == 0 {
                    lean_ctor_set(v___x_5247_, 0, v___x_5249_);
                    v___x_5251_ = v___x_5247_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
                    v___x_5251_ = v_reuseFailAlloc_5252_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5251_;
            }
            7 => {
                if v_isShared_5258_ == 0 {
                    v___x_5260_ = v___x_5257_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
                    v___x_5260_ = v_reuseFailAlloc_5261_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5260_;
            }
            9 => {
                return v___x_5264_;
            }
            10 => {
                if v_isShared_5272_ == 0 {
                    v___x_5274_ = v___x_5271_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
                    v___x_5274_ = v_reuseFailAlloc_5275_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0___redArg___boxed(
    mut v_x_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5283_: *mut LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0___redArg(
        v_x_5277_,
        v___y_5278_,
        v___y_5279_,
        v___y_5280_,
        v___y_5281_,
    );
    lean_dec(v___y_5281_);
    lean_dec_ref(v___y_5280_);
    lean_dec(v___y_5279_);
    lean_dec_ref(v___y_5278_);
    return v_res_5283_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0(
    mut v_00_u03b1_5284_: *mut LeanObject,
    mut v_x_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
    mut v___y_5287_: *mut LeanObject,
    mut v___y_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    v___x_5291_ = l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0___redArg(
        v_x_5285_,
        v___y_5286_,
        v___y_5287_,
        v___y_5288_,
        v___y_5289_,
    );
    return v___x_5291_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0___boxed(
    mut v_00_u03b1_5292_: *mut LeanObject,
    mut v_x_5293_: *mut LeanObject,
    mut v___y_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
    mut v___y_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5299_: *mut LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0(
        v_00_u03b1_5292_,
        v_x_5293_,
        v___y_5294_,
        v___y_5295_,
        v___y_5296_,
        v___y_5297_,
    );
    lean_dec(v___y_5297_);
    lean_dec_ref(v___y_5296_);
    lean_dec(v___y_5295_);
    lean_dec_ref(v___y_5294_);
    return v_res_5299_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    v___x_5301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__0;
    v___x_5302_ = l_Lean_stringToMessageData(v___x_5301_);
    return v___x_5302_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0(
    mut v___x_5303_: *mut LeanObject,
    mut v___x_5304_: u8,
    mut v___x_5305_: u8,
    mut v_mvarId_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: u8 = 0;
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5337_: u8 = 0;
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut v_a_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut v_a_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5359_: u8 = 0;
    let mut v_a_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5363_: u8 = 0;
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v_a_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5313_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v___x_5303_,
                    v___y_5308_,
                    v___y_5309_,
                    v___y_5310_,
                    v___y_5311_,
                );
                if lean_obj_tag(v___x_5313_) == 0 {
                    v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
                    lean_inc(v_a_5314_);
                    lean_dec_ref_known(v___x_5313_, 1);
                    v___x_5315_ = 0;
                    v___x_5316_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v___x_5316_, 0 as u32, v___x_5315_);
                    lean_ctor_set_uint8(v___x_5316_, 1 as u32, v___x_5304_);
                    lean_ctor_set_uint8(v___x_5316_, 2 as u32, v___x_5305_);
                    lean_ctor_set_uint8(v___x_5316_, 3 as u32, v___x_5304_);
                    v___x_5317_ = lean_box(0);
                    lean_inc_ref(v___x_5316_);
                    v___x_5318_ = l_Lean_MVarId_apply(
                        v_mvarId_5306_,
                        v_a_5314_,
                        v___x_5316_,
                        v___x_5317_,
                        v___y_5308_,
                        v___y_5309_,
                        v___y_5310_,
                        v___y_5311_,
                    );
                    if lean_obj_tag(v___x_5318_) == 0 {
                        v_a_5319_ = lean_ctor_get(v___x_5318_, 0);
                        lean_inc(v_a_5319_);
                        lean_dec_ref_known(v___x_5318_, 1);
                        if lean_obj_tag(v_a_5319_) == 1 {
                            v_tail_5327_ = lean_ctor_get(v_a_5319_, 1);
                            lean_inc(v_tail_5327_);
                            if lean_obj_tag(v_tail_5327_) == 1 {
                                v_tail_5328_ = lean_ctor_get(v_tail_5327_, 1);
                                if lean_obj_tag(v_tail_5328_) == 0 {
                                    v_head_5329_ = lean_ctor_get(v_a_5319_, 0);
                                    lean_inc(v_head_5329_);
                                    lean_dec_ref_known(v_a_5319_, 2);
                                    v_head_5330_ = lean_ctor_get(v_tail_5327_, 0);
                                    lean_inc(v_head_5330_);
                                    lean_dec_ref_known(v_tail_5327_, 2);
                                    v___x_5331_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                                        v_a_5307_,
                                        v___y_5308_,
                                        v___y_5309_,
                                        v___y_5310_,
                                        v___y_5311_,
                                    );
                                    if lean_obj_tag(v___x_5331_) == 0 {
                                        v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
                                        lean_inc(v_a_5332_);
                                        lean_dec_ref_known(v___x_5331_, 1);
                                        v___x_5333_ = l_Lean_MVarId_apply(
                                            v_head_5330_,
                                            v_a_5332_,
                                            v___x_5316_,
                                            v___x_5317_,
                                            v___y_5308_,
                                            v___y_5309_,
                                            v___y_5310_,
                                            v___y_5311_,
                                        );
                                        if lean_obj_tag(v___x_5333_) == 0 {
                                            v_a_5334_ = lean_ctor_get(v___x_5333_, 0);
                                            v_isSharedCheck_5343_ =
                                                (!lean_is_exclusive(v___x_5333_)) as u8;
                                            if v_isSharedCheck_5343_ == 0 {
                                                v___x_5336_ = v___x_5333_;
                                                v_isShared_5337_ = v_isSharedCheck_5343_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5334_);
                                                lean_dec(v___x_5333_);
                                                v___x_5336_ = lean_box(0);
                                                v_isShared_5337_ = v_isSharedCheck_5343_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_head_5329_);
                                            v_a_5344_ = lean_ctor_get(v___x_5333_, 0);
                                            v_isSharedCheck_5351_ =
                                                (!lean_is_exclusive(v___x_5333_)) as u8;
                                            if v_isSharedCheck_5351_ == 0 {
                                                v___x_5346_ = v___x_5333_;
                                                v_isShared_5347_ = v_isSharedCheck_5351_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5344_);
                                                lean_dec(v___x_5333_);
                                                v___x_5346_ = lean_box(0);
                                                v_isShared_5347_ = v_isSharedCheck_5351_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_head_5330_);
                                        lean_dec(v_head_5329_);
                                        lean_dec_ref_known(v___x_5316_, 0);
                                        v_a_5352_ = lean_ctor_get(v___x_5331_, 0);
                                        v_isSharedCheck_5359_ =
                                            (!lean_is_exclusive(v___x_5331_)) as u8;
                                        if v_isSharedCheck_5359_ == 0 {
                                            v___x_5354_ = v___x_5331_;
                                            v_isShared_5355_ = v_isSharedCheck_5359_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5352_);
                                            lean_dec(v___x_5331_);
                                            v___x_5354_ = lean_box(0);
                                            v_isShared_5355_ = v_isSharedCheck_5359_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_tail_5327_, 2);
                                    lean_dec_ref_known(v_a_5319_, 2);
                                    lean_dec_ref_known(v___x_5316_, 0);
                                    lean_dec(v_a_5307_);
                                    v___y_5321_ = v___y_5308_;
                                    v___y_5322_ = v___y_5309_;
                                    v___y_5323_ = v___y_5310_;
                                    v___y_5324_ = v___y_5311_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_a_5319_, 2);
                                lean_dec(v_tail_5327_);
                                lean_dec_ref_known(v___x_5316_, 0);
                                lean_dec(v_a_5307_);
                                v___y_5321_ = v___y_5308_;
                                v___y_5322_ = v___y_5309_;
                                v___y_5323_ = v___y_5310_;
                                v___y_5324_ = v___y_5311_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5319_);
                            lean_dec_ref_known(v___x_5316_, 0);
                            lean_dec(v_a_5307_);
                            v___y_5321_ = v___y_5308_;
                            v___y_5322_ = v___y_5309_;
                            v___y_5323_ = v___y_5310_;
                            v___y_5324_ = v___y_5311_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_5316_, 0);
                        lean_dec(v_a_5307_);
                        v_a_5360_ = lean_ctor_get(v___x_5318_, 0);
                        v_isSharedCheck_5367_ = (!lean_is_exclusive(v___x_5318_)) as u8;
                        if v_isSharedCheck_5367_ == 0 {
                            v___x_5362_ = v___x_5318_;
                            v_isShared_5363_ = v_isSharedCheck_5367_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5360_);
                            lean_dec(v___x_5318_);
                            v___x_5362_ = lean_box(0);
                            v_isShared_5363_ = v_isSharedCheck_5367_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5307_);
                    lean_dec(v_mvarId_5306_);
                    v_a_5368_ = lean_ctor_get(v___x_5313_, 0);
                    v_isSharedCheck_5375_ = (!lean_is_exclusive(v___x_5313_)) as u8;
                    if v_isSharedCheck_5375_ == 0 {
                        v___x_5370_ = v___x_5313_;
                        v_isShared_5371_ = v_isSharedCheck_5375_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5368_);
                        lean_dec(v___x_5313_);
                        v___x_5370_ = lean_box(0);
                        v_isShared_5371_ = v_isSharedCheck_5375_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5325_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1);
                v___x_5326_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_5325_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
                return v___x_5326_;
            }
            2 => {
                if lean_obj_tag(v_a_5334_) == 0 {
                    if v_isShared_5337_ == 0 {
                        lean_ctor_set(v___x_5336_, 0, v_head_5329_);
                        v___x_5339_ = v___x_5336_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_head_5329_);
                        v___x_5339_ = v_reuseFailAlloc_5340_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5336_);
                    lean_dec(v_a_5334_);
                    lean_dec(v_head_5329_);
                    v___x_5341_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___closed__1);
                    v___x_5342_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__spec__3___redArg(v___x_5341_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
                    return v___x_5342_;
                }
            }
            3 => {
                return v___x_5339_;
            }
            4 => {
                if v_isShared_5347_ == 0 {
                    v___x_5349_ = v___x_5346_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
                    v___x_5349_ = v_reuseFailAlloc_5350_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5349_;
            }
            6 => {
                if v_isShared_5355_ == 0 {
                    v___x_5357_ = v___x_5354_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
                    v___x_5357_ = v_reuseFailAlloc_5358_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5357_;
            }
            8 => {
                if v_isShared_5363_ == 0 {
                    v___x_5365_ = v___x_5362_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
                    v___x_5365_ = v_reuseFailAlloc_5366_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5365_;
            }
            10 => {
                if v_isShared_5371_ == 0 {
                    v___x_5373_ = v___x_5370_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
                    v___x_5373_ = v_reuseFailAlloc_5374_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___boxed(
    mut v___x_5376_: *mut LeanObject,
    mut v___x_5377_: *mut LeanObject,
    mut v___x_5378_: *mut LeanObject,
    mut v_mvarId_5379_: *mut LeanObject,
    mut v_a_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6122__boxed_5386_: u8 = 0;
    let mut v___x_6123__boxed_5387_: u8 = 0;
    let mut v_res_5388_: *mut LeanObject = core::ptr::null_mut();
    v___x_6122__boxed_5386_ = (lean_unbox(v___x_5377_) as u8);
    v___x_6123__boxed_5387_ = (lean_unbox(v___x_5378_) as u8);
    v_res_5388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0(v___x_5376_, v___x_6122__boxed_5386_, v___x_6123__boxed_5387_, v_mvarId_5379_, v_a_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
    lean_dec(v___y_5384_);
    lean_dec_ref(v___y_5383_);
    lean_dec(v___y_5382_);
    lean_dec_ref(v___y_5381_);
    return v_res_5388_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1(
    mut v___x_5398_: u8,
    mut v_mvarId_5399_: *mut LeanObject,
    mut v_as_5400_: *mut LeanObject,
    mut v_sz_5401_: usize,
    mut v_i_5402_: usize,
    mut v_b_5403_: *mut LeanObject,
    mut v___y_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5409_: u8 = 0;
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5420_: u8 = 0;
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: usize = 0;
    let mut v___x_5428_: usize = 0;
    let mut v_isSharedCheck_5430_: u8 = 0;
    let mut v_a_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5409_ = lean_usize_dec_lt(v_i_5402_, v_sz_5401_);
                if v___x_5409_ == 0 {
                    lean_dec(v_mvarId_5399_);
                    v___x_5410_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5410_, 0, v_b_5403_);
                    return v___x_5410_;
                } else {
                    lean_dec_ref(v_b_5403_);
                    v_a_5411_ = lean_array_uget_borrowed(v_as_5400_, v_i_5402_);
                    v___x_5412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__1;
                    v___x_5413_ = lean_box((v___x_5409_) as usize);
                    v___x_5414_ = lean_box((v___x_5398_) as usize);
                    lean_inc(v_a_5411_);
                    lean_inc(v_mvarId_5399_);
                    v___f_5415_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                    lean_closure_set(v___f_5415_, 0, v___x_5412_);
                    lean_closure_set(v___f_5415_, 1, v___x_5413_);
                    lean_closure_set(v___f_5415_, 2, v___x_5414_);
                    lean_closure_set(v___f_5415_, 3, v_mvarId_5399_);
                    lean_closure_set(v___f_5415_, 4, v_a_5411_);
                    v___x_5416_ =
                        l_Lean_observing_x3f___at___00Lean_MVarId_liftReflToEq_spec__0___redArg(
                            v___f_5415_,
                            v___y_5404_,
                            v___y_5405_,
                            v___y_5406_,
                            v___y_5407_,
                        );
                    if lean_obj_tag(v___x_5416_) == 0 {
                        v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
                        v_isSharedCheck_5430_ = (!lean_is_exclusive(v___x_5416_)) as u8;
                        if v_isSharedCheck_5430_ == 0 {
                            v___x_5419_ = v___x_5416_;
                            v_isShared_5420_ = v_isSharedCheck_5430_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5417_);
                            lean_dec(v___x_5416_);
                            v___x_5419_ = lean_box(0);
                            v_isShared_5420_ = v_isSharedCheck_5430_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_mvarId_5399_);
                        v_a_5431_ = lean_ctor_get(v___x_5416_, 0);
                        v_isSharedCheck_5438_ = (!lean_is_exclusive(v___x_5416_)) as u8;
                        if v_isSharedCheck_5438_ == 0 {
                            v___x_5433_ = v___x_5416_;
                            v_isShared_5434_ = v_isSharedCheck_5438_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5431_);
                            lean_dec(v___x_5416_);
                            v___x_5433_ = lean_box(0);
                            v_isShared_5434_ = v_isSharedCheck_5438_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5421_ = lean_box(0);
                if lean_obj_tag(v_a_5417_) == 1 {
                    lean_dec(v_mvarId_5399_);
                    v___x_5422_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5422_, 0, v_a_5417_);
                    lean_ctor_set(v___x_5422_, 1, v___x_5421_);
                    if v_isShared_5420_ == 0 {
                        lean_ctor_set(v___x_5419_, 0, v___x_5422_);
                        v___x_5424_ = v___x_5419_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5422_);
                        v___x_5424_ = v_reuseFailAlloc_5425_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5419_);
                    lean_dec(v_a_5417_);
                    v___x_5426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__2;
                    v___x_5427_ = 1usize;
                    v___x_5428_ = lean_usize_add(v_i_5402_, v___x_5427_);
                    v_i_5402_ = v___x_5428_;
                    v_b_5403_ = v___x_5426_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_5424_;
            }
            3 => {
                if v_isShared_5434_ == 0 {
                    v___x_5436_ = v___x_5433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___boxed(
    mut v___x_5439_: *mut LeanObject,
    mut v_mvarId_5440_: *mut LeanObject,
    mut v_as_5441_: *mut LeanObject,
    mut v_sz_5442_: *mut LeanObject,
    mut v_i_5443_: *mut LeanObject,
    mut v_b_5444_: *mut LeanObject,
    mut v___y_5445_: *mut LeanObject,
    mut v___y_5446_: *mut LeanObject,
    mut v___y_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
    mut v___y_5449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6295__boxed_5450_: u8 = 0;
    let mut v_sz_boxed_5451_: usize = 0;
    let mut v_i_boxed_5452_: usize = 0;
    let mut v_res_5453_: *mut LeanObject = core::ptr::null_mut();
    v___x_6295__boxed_5450_ = (lean_unbox(v___x_5439_) as u8);
    v_sz_boxed_5451_ = lean_unbox_usize(v_sz_5442_);
    lean_dec(v_sz_5442_);
    v_i_boxed_5452_ = lean_unbox_usize(v_i_5443_);
    lean_dec(v_i_5443_);
    v_res_5453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1(v___x_6295__boxed_5450_, v_mvarId_5440_, v_as_5441_, v_sz_boxed_5451_, v_i_boxed_5452_, v_b_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
    lean_dec(v___y_5448_);
    lean_dec_ref(v___y_5447_);
    lean_dec(v___y_5446_);
    lean_dec_ref(v___y_5445_);
    lean_dec_ref(v_as_5441_);
    return v_res_5453_;
}
pub unsafe fn l_Lean_MVarId_liftReflToEq(
    mut v_mvarId_5457_: *mut LeanObject,
    mut v_a_5458_: *mut LeanObject,
    mut v_a_5459_: *mut LeanObject,
    mut v_a_5460_: *mut LeanObject,
    mut v_a_5461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5466_: u8 = 0;
    let mut v_ctxApprox_5467_: u8 = 0;
    let mut v_quasiPatternApprox_5468_: u8 = 0;
    let mut v_constApprox_5469_: u8 = 0;
    let mut v_isDefEqStuckEx_5470_: u8 = 0;
    let mut v_unificationHints_5471_: u8 = 0;
    let mut v_proofIrrelevance_5472_: u8 = 0;
    let mut v_assignSyntheticOpaque_5473_: u8 = 0;
    let mut v_offsetCnstrs_5474_: u8 = 0;
    let mut v_etaStruct_5475_: u8 = 0;
    let mut v_univApprox_5476_: u8 = 0;
    let mut v_iota_5477_: u8 = 0;
    let mut v_beta_5478_: u8 = 0;
    let mut v_proj_5479_: u8 = 0;
    let mut v_zeta_5480_: u8 = 0;
    let mut v_zetaDelta_5481_: u8 = 0;
    let mut v_zetaUnused_5482_: u8 = 0;
    let mut v_zetaHave_5483_: u8 = 0;
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v_trackZetaDelta_5487_: u8 = 0;
    let mut v_zetaDeltaSet_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5494_: u8 = 0;
    let mut v_inTypeClassResolution_5495_: u8 = 0;
    let mut v_cacheInferType_5496_: u8 = 0;
    let mut v___x_5497_: u8 = 0;
    let mut v_config_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: u64 = 0;
    let mut v___x_5501_: u64 = 0;
    let mut v___x_5502_: u64 = 0;
    let mut v___x_5503_: u64 = 0;
    let mut v___x_5504_: u64 = 0;
    let mut v_key_5505_: u64 = 0;
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5512_: u8 = 0;
    let mut v_fn_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5528_: usize = 0;
    let mut v___x_5529_: usize = 0;
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v_fst_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5543_: u8 = 0;
    let mut v_a_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5551_: u8 = 0;
    let mut v_a_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5555_: u8 = 0;
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5559_: u8 = 0;
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut v_a_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5573_: u8 = 0;
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut v_reuseFailAlloc_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5463_ = l_Lean_MVarId_liftReflToEq___closed__1;
                lean_inc(v_mvarId_5457_);
                v___x_5464_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5457_,
                    v___x_5463_,
                    v_a_5458_,
                    v_a_5459_,
                    v_a_5460_,
                    v_a_5461_,
                );
                if lean_obj_tag(v___x_5464_) == 0 {
                    lean_dec_ref_known(v___x_5464_, 1);
                    v___x_5465_ = l_Lean_Meta_Context_config(v_a_5458_);
                    v_foApprox_5466_ = lean_ctor_get_uint8(v___x_5465_, 0 as u32);
                    v_ctxApprox_5467_ = lean_ctor_get_uint8(v___x_5465_, 1 as u32);
                    v_quasiPatternApprox_5468_ = lean_ctor_get_uint8(v___x_5465_, 2 as u32);
                    v_constApprox_5469_ = lean_ctor_get_uint8(v___x_5465_, 3 as u32);
                    v_isDefEqStuckEx_5470_ = lean_ctor_get_uint8(v___x_5465_, 4 as u32);
                    v_unificationHints_5471_ = lean_ctor_get_uint8(v___x_5465_, 5 as u32);
                    v_proofIrrelevance_5472_ = lean_ctor_get_uint8(v___x_5465_, 6 as u32);
                    v_assignSyntheticOpaque_5473_ = lean_ctor_get_uint8(v___x_5465_, 7 as u32);
                    v_offsetCnstrs_5474_ = lean_ctor_get_uint8(v___x_5465_, 8 as u32);
                    v_etaStruct_5475_ = lean_ctor_get_uint8(v___x_5465_, 10 as u32);
                    v_univApprox_5476_ = lean_ctor_get_uint8(v___x_5465_, 11 as u32);
                    v_iota_5477_ = lean_ctor_get_uint8(v___x_5465_, 12 as u32);
                    v_beta_5478_ = lean_ctor_get_uint8(v___x_5465_, 13 as u32);
                    v_proj_5479_ = lean_ctor_get_uint8(v___x_5465_, 14 as u32);
                    v_zeta_5480_ = lean_ctor_get_uint8(v___x_5465_, 15 as u32);
                    v_zetaDelta_5481_ = lean_ctor_get_uint8(v___x_5465_, 16 as u32);
                    v_zetaUnused_5482_ = lean_ctor_get_uint8(v___x_5465_, 17 as u32);
                    v_zetaHave_5483_ = lean_ctor_get_uint8(v___x_5465_, 18 as u32);
                    v_isSharedCheck_5579_ = (!lean_is_exclusive(v___x_5465_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v___x_5485_ = v___x_5465_;
                        v_isShared_5486_ = v_isSharedCheck_5579_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5465_);
                        v___x_5485_ = lean_box(0);
                        v_isShared_5486_ = v_isSharedCheck_5579_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_5457_);
                    v_a_5580_ = lean_ctor_get(v___x_5464_, 0);
                    v_isSharedCheck_5587_ = (!lean_is_exclusive(v___x_5464_)) as u8;
                    if v_isSharedCheck_5587_ == 0 {
                        v___x_5582_ = v___x_5464_;
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_5580_);
                        lean_dec(v___x_5464_);
                        v___x_5582_ = lean_box(0);
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_5487_ = lean_ctor_get_uint8(
                    v_a_5458_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5488_ = lean_ctor_get(v_a_5458_, 1);
                v_lctx_5489_ = lean_ctor_get(v_a_5458_, 2);
                v_localInstances_5490_ = lean_ctor_get(v_a_5458_, 3);
                v_defEqCtx_x3f_5491_ = lean_ctor_get(v_a_5458_, 4);
                v_synthPendingDepth_5492_ = lean_ctor_get(v_a_5458_, 5);
                v_canUnfold_x3f_5493_ = lean_ctor_get(v_a_5458_, 6);
                v_univApprox_5494_ = lean_ctor_get_uint8(
                    v_a_5458_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5495_ = lean_ctor_get_uint8(
                    v_a_5458_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5496_ = lean_ctor_get_uint8(
                    v_a_5458_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_5497_ = 2;
                if v_isShared_5486_ == 0 {
                    v_config_5499_ = v___x_5485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 0 as u32, v_foApprox_5466_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 1 as u32, v_ctxApprox_5467_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5578_,
                        2 as u32,
                        v_quasiPatternApprox_5468_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 3 as u32, v_constApprox_5469_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 4 as u32, v_isDefEqStuckEx_5470_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 5 as u32, v_unificationHints_5471_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 6 as u32, v_proofIrrelevance_5472_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5578_,
                        7 as u32,
                        v_assignSyntheticOpaque_5473_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 8 as u32, v_offsetCnstrs_5474_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 10 as u32, v_etaStruct_5475_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 11 as u32, v_univApprox_5476_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 12 as u32, v_iota_5477_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 13 as u32, v_beta_5478_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 14 as u32, v_proj_5479_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 15 as u32, v_zeta_5480_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 16 as u32, v_zetaDelta_5481_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 17 as u32, v_zetaUnused_5482_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5578_, 18 as u32, v_zetaHave_5483_);
                    v_config_5499_ = v_reuseFailAlloc_5578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_5499_, 9 as u32, v___x_5497_);
                v___x_5500_ = l_Lean_Meta_Context_configKey(v_a_5458_);
                v___x_5501_ = 3u64;
                v___x_5502_ = lean_uint64_shift_right(v___x_5500_, v___x_5501_);
                v___x_5503_ = lean_uint64_shift_left(v___x_5502_, v___x_5501_);
                v___x_5504_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___lam__3___closed__7_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_);
                v_key_5505_ = lean_uint64_lor(v___x_5503_, v___x_5504_);
                v___x_5506_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5506_, 0, v_config_5499_);
                lean_ctor_set_uint64(
                    v___x_5506_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_5505_,
                );
                lean_inc(v_canUnfold_x3f_5493_);
                lean_inc(v_synthPendingDepth_5492_);
                lean_inc(v_defEqCtx_x3f_5491_);
                lean_inc_ref(v_localInstances_5490_);
                lean_inc_ref(v_lctx_5489_);
                lean_inc(v_zetaDeltaSet_5488_);
                v___x_5507_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5507_, 0, v___x_5506_);
                lean_ctor_set(v___x_5507_, 1, v_zetaDeltaSet_5488_);
                lean_ctor_set(v___x_5507_, 2, v_lctx_5489_);
                lean_ctor_set(v___x_5507_, 3, v_localInstances_5490_);
                lean_ctor_set(v___x_5507_, 4, v_defEqCtx_x3f_5491_);
                lean_ctor_set(v___x_5507_, 5, v_synthPendingDepth_5492_);
                lean_ctor_set(v___x_5507_, 6, v_canUnfold_x3f_5493_);
                lean_ctor_set_uint8(
                    v___x_5507_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5487_,
                );
                lean_ctor_set_uint8(
                    v___x_5507_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5494_,
                );
                lean_ctor_set_uint8(
                    v___x_5507_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5495_,
                );
                lean_ctor_set_uint8(
                    v___x_5507_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5496_,
                );
                lean_inc(v_mvarId_5457_);
                v___x_5508_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_5457_,
                    v___x_5507_,
                    v_a_5459_,
                    v_a_5460_,
                    v_a_5461_,
                );
                lean_dec_ref_known(v___x_5507_, 7);
                if lean_obj_tag(v___x_5508_) == 0 {
                    v_a_5509_ = lean_ctor_get(v___x_5508_, 0);
                    v_isSharedCheck_5569_ = (!lean_is_exclusive(v___x_5508_)) as u8;
                    if v_isSharedCheck_5569_ == 0 {
                        v___x_5511_ = v___x_5508_;
                        v_isShared_5512_ = v_isSharedCheck_5569_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5509_);
                        lean_dec(v___x_5508_);
                        v___x_5511_ = lean_box(0);
                        v_isShared_5512_ = v_isSharedCheck_5569_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_5457_);
                    v_a_5570_ = lean_ctor_get(v___x_5508_, 0);
                    v_isSharedCheck_5577_ = (!lean_is_exclusive(v___x_5508_)) as u8;
                    if v_isSharedCheck_5577_ == 0 {
                        v___x_5572_ = v___x_5508_;
                        v_isShared_5573_ = v_isSharedCheck_5577_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5570_);
                        lean_dec(v___x_5508_);
                        v___x_5572_ = lean_box(0);
                        v_isShared_5573_ = v_isSharedCheck_5577_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_5509_) == 5 {
                    v_fn_5513_ = lean_ctor_get(v_a_5509_, 0);
                    lean_inc_ref(v_fn_5513_);
                    lean_dec_ref_known(v_a_5509_, 2);
                    if lean_obj_tag(v_fn_5513_) == 5 {
                        v_fn_5514_ = lean_ctor_get(v_fn_5513_, 0);
                        lean_inc_ref(v_fn_5514_);
                        lean_dec_ref_known(v_fn_5513_, 2);
                        v___x_5515_ = l_Lean_MVarId_applyRfl___lam__1___closed__0;
                        v___x_5516_ = l_Lean_Expr_isAppOf(v_fn_5514_, v___x_5515_);
                        if v___x_5516_ == 0 {
                            lean_del_object(v___x_5511_);
                            v___x_5517_ = lean_st_ref_get(v_a_5461_);
                            v_env_5518_ = lean_ctor_get(v___x_5517_, 0);
                            lean_inc_ref(v_env_5518_);
                            lean_dec(v___x_5517_);
                            v___x_5519_ = l_Lean_Meta_Rfl_reflExt;
                            v_ext_5520_ = lean_ctor_get(v___x_5519_, 1);
                            v_toEnvExtension_5521_ = lean_ctor_get(v_ext_5520_, 0);
                            v_asyncMode_5522_ = lean_ctor_get(v_toEnvExtension_5521_, 2);
                            v___x_5523_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2__spec__0_spec__3___closed__0);
                            v___x_5524_ = l_Lean_ScopedEnvExtension_getState___redArg(
                                v___x_5523_,
                                v___x_5519_,
                                v_env_5518_,
                                v_asyncMode_5522_,
                            );
                            v___x_5525_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
                                v___x_5524_,
                                v_fn_5514_,
                                v_a_5458_,
                                v_a_5459_,
                                v_a_5460_,
                                v_a_5461_,
                            );
                            lean_dec(v___x_5524_);
                            if lean_obj_tag(v___x_5525_) == 0 {
                                v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
                                lean_inc(v_a_5526_);
                                lean_dec_ref_known(v___x_5525_, 1);
                                v___x_5527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1___closed__2;
                                v_sz_5528_ = lean_array_size(v_a_5526_);
                                v___x_5529_ = 0usize;
                                lean_inc(v_mvarId_5457_);
                                v___x_5530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_liftReflToEq_spec__1(v___x_5516_, v_mvarId_5457_, v_a_5526_, v_sz_5528_, v___x_5529_, v___x_5527_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_);
                                lean_dec(v_a_5526_);
                                if lean_obj_tag(v___x_5530_) == 0 {
                                    v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
                                    v_isSharedCheck_5543_ = (!lean_is_exclusive(v___x_5530_)) as u8;
                                    if v_isSharedCheck_5543_ == 0 {
                                        v___x_5533_ = v___x_5530_;
                                        v_isShared_5534_ = v_isSharedCheck_5543_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5531_);
                                        lean_dec(v___x_5530_);
                                        v___x_5533_ = lean_box(0);
                                        v_isShared_5534_ = v_isSharedCheck_5543_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_mvarId_5457_);
                                    v_a_5544_ = lean_ctor_get(v___x_5530_, 0);
                                    v_isSharedCheck_5551_ = (!lean_is_exclusive(v___x_5530_)) as u8;
                                    if v_isSharedCheck_5551_ == 0 {
                                        v___x_5546_ = v___x_5530_;
                                        v_isShared_5547_ = v_isSharedCheck_5551_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5544_);
                                        lean_dec(v___x_5530_);
                                        v___x_5546_ = lean_box(0);
                                        v_isShared_5547_ = v_isSharedCheck_5551_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_mvarId_5457_);
                                v_a_5552_ = lean_ctor_get(v___x_5525_, 0);
                                v_isSharedCheck_5559_ = (!lean_is_exclusive(v___x_5525_)) as u8;
                                if v_isSharedCheck_5559_ == 0 {
                                    v___x_5554_ = v___x_5525_;
                                    v_isShared_5555_ = v_isSharedCheck_5559_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5552_);
                                    lean_dec(v___x_5525_);
                                    v___x_5554_ = lean_box(0);
                                    v_isShared_5555_ = v_isSharedCheck_5559_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_fn_5514_);
                            if v_isShared_5512_ == 0 {
                                lean_ctor_set(v___x_5511_, 0, v_mvarId_5457_);
                                v___x_5561_ = v___x_5511_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_5562_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_mvarId_5457_);
                                v___x_5561_ = v_reuseFailAlloc_5562_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_fn_5513_);
                        if v_isShared_5512_ == 0 {
                            lean_ctor_set(v___x_5511_, 0, v_mvarId_5457_);
                            v___x_5564_ = v___x_5511_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_mvarId_5457_);
                            v___x_5564_ = v_reuseFailAlloc_5565_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5509_);
                    if v_isShared_5512_ == 0 {
                        lean_ctor_set(v___x_5511_, 0, v_mvarId_5457_);
                        v___x_5567_ = v___x_5511_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_mvarId_5457_);
                        v___x_5567_ = v_reuseFailAlloc_5568_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_5535_ = lean_ctor_get(v_a_5531_, 0);
                lean_inc(v_fst_5535_);
                lean_dec(v_a_5531_);
                if lean_obj_tag(v_fst_5535_) == 0 {
                    if v_isShared_5534_ == 0 {
                        lean_ctor_set(v___x_5533_, 0, v_mvarId_5457_);
                        v___x_5537_ = v___x_5533_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_mvarId_5457_);
                        v___x_5537_ = v_reuseFailAlloc_5538_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_5457_);
                    v_val_5539_ = lean_ctor_get(v_fst_5535_, 0);
                    lean_inc(v_val_5539_);
                    lean_dec_ref_known(v_fst_5535_, 1);
                    if v_isShared_5534_ == 0 {
                        lean_ctor_set(v___x_5533_, 0, v_val_5539_);
                        v___x_5541_ = v___x_5533_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_val_5539_);
                        v___x_5541_ = v_reuseFailAlloc_5542_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5537_;
            }
            6 => {
                return v___x_5541_;
            }
            7 => {
                if v_isShared_5547_ == 0 {
                    v___x_5549_ = v___x_5546_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
                    v___x_5549_ = v_reuseFailAlloc_5550_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5549_;
            }
            9 => {
                if v_isShared_5555_ == 0 {
                    v___x_5557_ = v___x_5554_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5552_);
                    v___x_5557_ = v_reuseFailAlloc_5558_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5557_;
            }
            11 => {
                return v___x_5561_;
            }
            12 => {
                return v___x_5564_;
            }
            13 => {
                return v___x_5567_;
            }
            14 => {
                if v_isShared_5573_ == 0 {
                    v___x_5575_ = v___x_5572_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_a_5570_);
                    v___x_5575_ = v_reuseFailAlloc_5576_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5575_;
            }
            16 => {
                if v_isShared_5583_ == 0 {
                    v___x_5585_ = v___x_5582_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
                    v___x_5585_ = v_reuseFailAlloc_5586_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_liftReflToEq___boxed(
    mut v_mvarId_5588_: *mut LeanObject,
    mut v_a_5589_: *mut LeanObject,
    mut v_a_5590_: *mut LeanObject,
    mut v_a_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5594_: *mut LeanObject = core::ptr::null_mut();
    v_res_5594_ =
        l_Lean_MVarId_liftReflToEq(v_mvarId_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
    lean_dec(v_a_5592_);
    lean_dec_ref(v_a_5591_);
    lean_dec(v_a_5590_);
    lean_dec_ref(v_a_5589_);
    return v_res_5594_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Rfl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_1712517898____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Rfl_reflExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Rfl_reflExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn___regBuiltin___private_Lean_Meta_Tactic_Rfl_0__Lean_Meta_Rfl_initFn_docString__1_00___x40_Lean_Meta_Tactic_Rfl_914023288____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Rfl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Rfl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Rfl(builtin);
}
