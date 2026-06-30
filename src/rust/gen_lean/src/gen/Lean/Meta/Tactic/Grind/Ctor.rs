// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Ctor
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Injective Lean.Meta.Tactic.Grind.Simp
use crate::ffi::{
    lean_array_get, lean_array_set, lean_expr_eqv, lean_grind_internalize, lean_grind_mk_eq_proof,
    lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_st_ref_get, lean_uint64_lor,
    lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_zipWith___at___00List_zip_spec__0;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_containsOnBranch, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getForallArity, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppOptM, l_Lean_Meta_mkEq, l_Lean_Meta_mkExpectedPropHint,
    l_Lean_Meta_mkExpectedTypeHint, l_Lean_Meta_mkHEq, l_Lean_Meta_mkNoConfusion,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isDefEqD, l_Lean_Meta_isLevelDefEq, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::Injective::{
    initialize_Lean_Meta_Injective, l_Lean_Meta_getCtorAppIndices_x3f,
    l_Lean_Meta_mkHInjectiveTheoremNameFor, l_Lean_Meta_mkInjectiveTheoremNameFor,
    runtime_initialize_Lean_Meta_Injective,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_getFalseExpr___redArg,
    l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_addNewRawFact,
    l_Lean_Meta_Grind_closeGoal, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_pushEqCore___redArg, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_executeReservedNameAction;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 106, 101, 99, 116, 105, 118, 105, 116, 121, 32, 116, 104, 101, 111, 114, 101, 109, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2_value) as *mut leanh::LeanObject,9743492140944907313 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6_value) as *mut leanh::LeanObject,13589827700912665667 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 111, 67, 111, 110, 102, 117, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1: u64 = 0;
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ =
        l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0;
    v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(
    mut v_eqs_1504_: *mut leanh::LeanObject,
    mut v_proof_1505_: *mut leanh::LeanObject,
    mut v_generation_1506_: *mut leanh::LeanObject,
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
    mut v_a_1509_: *mut leanh::LeanObject,
    mut v_a_1510_: *mut leanh::LeanObject,
    mut v_a_1511_: *mut leanh::LeanObject,
    mut v_a_1512_: *mut leanh::LeanObject,
    mut v_a_1513_: *mut leanh::LeanObject,
    mut v_a_1514_: *mut leanh::LeanObject,
    mut v_a_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1540_: u8 = 0;
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v_arg_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v_arg_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1554_: u8 = 0;
    let mut v_arg_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_a_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_a_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_a_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_eqs_1504_);
                v___x_1521_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_eqs_1504_, v_a_1514_);
                if leanh::lean_obj_tag(v___x_1521_) == 0 {
                    v_a_1522_ = leanh::lean_ctor_get(v___x_1521_, 0);
                    leanh::lean_inc(v_a_1522_);
                    leanh::lean_dec_ref_known(v___x_1521_, 1);
                    v___x_1545_ = l_Lean_Expr_cleanupAnnotations(v_a_1522_);
                    v___x_1546_ = l_Lean_Expr_isApp(v___x_1545_);
                    if v___x_1546_ == 0 {
                        leanh::lean_dec_ref(v___x_1545_);
                        leanh::lean_dec(v_generation_1506_);
                        leanh::lean_dec_ref(v_proof_1505_);
                        v___y_1524_ = v_a_1511_;
                        v___y_1525_ = v_a_1512_;
                        v___y_1526_ = v_a_1513_;
                        v___y_1527_ = v_a_1514_;
                        v___y_1528_ = v_a_1515_;
                        v___y_1529_ = v_a_1516_;
                        state = 2;
                        continue;
                    } else {
                        v_arg_1547_ = leanh::lean_ctor_get(v___x_1545_, 1);
                        leanh::lean_inc_ref(v_arg_1547_);
                        v___x_1548_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1545_);
                        v___x_1549_ = l_Lean_Expr_isApp(v___x_1548_);
                        if v___x_1549_ == 0 {
                            leanh::lean_dec_ref(v___x_1548_);
                            leanh::lean_dec_ref(v_arg_1547_);
                            leanh::lean_dec(v_generation_1506_);
                            leanh::lean_dec_ref(v_proof_1505_);
                            v___y_1524_ = v_a_1511_;
                            v___y_1525_ = v_a_1512_;
                            v___y_1526_ = v_a_1513_;
                            v___y_1527_ = v_a_1514_;
                            v___y_1528_ = v_a_1515_;
                            v___y_1529_ = v_a_1516_;
                            state = 2;
                            continue;
                        } else {
                            v_arg_1550_ = leanh::lean_ctor_get(v___x_1548_, 1);
                            leanh::lean_inc_ref(v_arg_1550_);
                            v___x_1551_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1548_);
                            v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3;
                            v___x_1553_ = l_Lean_Expr_isConstOf(v___x_1551_, v___x_1552_);
                            if v___x_1553_ == 0 {
                                v___x_1554_ = l_Lean_Expr_isApp(v___x_1551_);
                                if v___x_1554_ == 0 {
                                    leanh::lean_dec_ref(v___x_1551_);
                                    leanh::lean_dec_ref(v_arg_1550_);
                                    leanh::lean_dec_ref(v_arg_1547_);
                                    leanh::lean_dec(v_generation_1506_);
                                    leanh::lean_dec_ref(v_proof_1505_);
                                    v___y_1524_ = v_a_1511_;
                                    v___y_1525_ = v_a_1512_;
                                    v___y_1526_ = v_a_1513_;
                                    v___y_1527_ = v_a_1514_;
                                    v___y_1528_ = v_a_1515_;
                                    v___y_1529_ = v_a_1516_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_1555_ = leanh::lean_ctor_get(v___x_1551_, 1);
                                    leanh::lean_inc_ref(v_arg_1555_);
                                    v___x_1556_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1551_);
                                    v___x_1557_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5;
                                    v___x_1558_ = l_Lean_Expr_isConstOf(v___x_1556_, v___x_1557_);
                                    if v___x_1558_ == 0 {
                                        leanh::lean_dec_ref(v_arg_1550_);
                                        v___x_1559_ = l_Lean_Expr_isApp(v___x_1556_);
                                        if v___x_1559_ == 0 {
                                            leanh::lean_dec_ref(v___x_1556_);
                                            leanh::lean_dec_ref(v_arg_1555_);
                                            leanh::lean_dec_ref(v_arg_1547_);
                                            leanh::lean_dec(v_generation_1506_);
                                            leanh::lean_dec_ref(v_proof_1505_);
                                            v___y_1524_ = v_a_1511_;
                                            v___y_1525_ = v_a_1512_;
                                            v___y_1526_ = v_a_1513_;
                                            v___y_1527_ = v_a_1514_;
                                            v___y_1528_ = v_a_1515_;
                                            v___y_1529_ = v_a_1516_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_1560_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_1556_);
                                            v___x_1561_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7;
                                            v___x_1562_ =
                                                l_Lean_Expr_isConstOf(v___x_1560_, v___x_1561_);
                                            leanh::lean_dec_ref(v___x_1560_);
                                            if v___x_1562_ == 0 {
                                                leanh::lean_dec_ref(v_arg_1555_);
                                                leanh::lean_dec_ref(v_arg_1547_);
                                                leanh::lean_dec(v_generation_1506_);
                                                leanh::lean_dec_ref(v_proof_1505_);
                                                v___y_1524_ = v_a_1511_;
                                                v___y_1525_ = v_a_1512_;
                                                v___y_1526_ = v_a_1513_;
                                                v___y_1527_ = v_a_1514_;
                                                v___y_1528_ = v_a_1515_;
                                                v___y_1529_ = v_a_1516_;
                                                state = 2;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v_eqs_1504_);
                                                v___x_1563_ =
                                                    l_Lean_Meta_Grind_preprocessLight___redArg(
                                                        v_arg_1555_,
                                                        v_a_1508_,
                                                        v_a_1509_,
                                                        v_a_1510_,
                                                        v_a_1511_,
                                                        v_a_1512_,
                                                        v_a_1513_,
                                                        v_a_1514_,
                                                        v_a_1515_,
                                                        v_a_1516_,
                                                    );
                                                if leanh::lean_obj_tag(v___x_1563_) == 0 {
                                                    v_a_1564_ =
                                                        leanh::lean_ctor_get(v___x_1563_, 0);
                                                    leanh::lean_inc(v_a_1564_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_1563_,
                                                        1,
                                                    );
                                                    v___x_1565_ =
                                                        l_Lean_Meta_Grind_preprocessLight___redArg(
                                                            v_arg_1547_,
                                                            v_a_1508_,
                                                            v_a_1509_,
                                                            v_a_1510_,
                                                            v_a_1511_,
                                                            v_a_1512_,
                                                            v_a_1513_,
                                                            v_a_1514_,
                                                            v_a_1515_,
                                                            v_a_1516_,
                                                        );
                                                    if leanh::lean_obj_tag(v___x_1565_) == 0
                                                    {
                                                        v_a_1566_ = leanh::lean_ctor_get(
                                                            v___x_1565_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_1566_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_1565_,
                                                            1,
                                                        );
                                                        v___x_1567_ = leanh::lean_box(0);
                                                        leanh::lean_inc(v_a_1516_);
                                                        leanh::lean_inc_ref(v_a_1515_);
                                                        leanh::lean_inc(v_a_1514_);
                                                        leanh::lean_inc_ref(v_a_1513_);
                                                        leanh::lean_inc(v_a_1512_);
                                                        leanh::lean_inc_ref(v_a_1511_);
                                                        leanh::lean_inc(v_a_1510_);
                                                        leanh::lean_inc_ref(v_a_1509_);
                                                        leanh::lean_inc(v_a_1508_);
                                                        leanh::lean_inc(v_a_1507_);
                                                        leanh::lean_inc(v_generation_1506_);
                                                        leanh::lean_inc(v_a_1564_);
                                                        v___x_1568_ = lean_grind_internalize(
                                                            v_a_1564_,
                                                            v_generation_1506_,
                                                            v___x_1567_,
                                                            v_a_1507_,
                                                            v_a_1508_,
                                                            v_a_1509_,
                                                            v_a_1510_,
                                                            v_a_1511_,
                                                            v_a_1512_,
                                                            v_a_1513_,
                                                            v_a_1514_,
                                                            v_a_1515_,
                                                            v_a_1516_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_1568_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec_ref_known(
                                                                v___x_1568_,
                                                                1,
                                                            );
                                                            leanh::lean_inc(v_a_1516_);
                                                            leanh::lean_inc_ref(v_a_1515_);
                                                            leanh::lean_inc(v_a_1514_);
                                                            leanh::lean_inc_ref(v_a_1513_);
                                                            leanh::lean_inc(v_a_1512_);
                                                            leanh::lean_inc_ref(v_a_1511_);
                                                            leanh::lean_inc(v_a_1510_);
                                                            leanh::lean_inc_ref(v_a_1509_);
                                                            leanh::lean_inc(v_a_1508_);
                                                            leanh::lean_inc(v_a_1507_);
                                                            leanh::lean_inc(v_a_1566_);
                                                            v___x_1569_ = lean_grind_internalize(
                                                                v_a_1566_,
                                                                v_generation_1506_,
                                                                v___x_1567_,
                                                                v_a_1507_,
                                                                v_a_1508_,
                                                                v_a_1509_,
                                                                v_a_1510_,
                                                                v_a_1511_,
                                                                v_a_1512_,
                                                                v_a_1513_,
                                                                v_a_1514_,
                                                                v_a_1515_,
                                                                v_a_1516_,
                                                            );
                                                            if leanh::lean_obj_tag(
                                                                v___x_1569_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_1569_,
                                                                    1,
                                                                );
                                                                leanh::lean_inc(v_a_1566_);
                                                                leanh::lean_inc(v_a_1564_);
                                                                v___x_1570_ = l_Lean_Meta_mkHEq(
                                                                    v_a_1564_, v_a_1566_,
                                                                    v_a_1513_, v_a_1514_,
                                                                    v_a_1515_, v_a_1516_,
                                                                );
                                                                if leanh::lean_obj_tag(
                                                                    v___x_1570_,
                                                                ) == 0
                                                                {
                                                                    v_a_1571_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_1570_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_a_1571_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v___x_1570_, 1);
                                                                    v___x_1572_ = l_Lean_Meta_mkExpectedPropHint(v_proof_1505_, v_a_1571_);
                                                                    v___x_1573_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1564_, v_a_1566_, v___x_1572_, v___x_1562_, v_a_1507_, v_a_1509_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
                                                                    return v___x_1573_;
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_a_1566_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_1564_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_proof_1505_,
                                                                    );
                                                                    v_a_1574_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_1570_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1581_ = (!leanh::lean_is_exclusive(v___x_1570_)) as u8;
                                                                    if v_isSharedCheck_1581_ == 0 {
                                                                        v___x_1576_ = v___x_1570_;
                                                                        v_isShared_1577_ =
                                                                            v_isSharedCheck_1581_;
                                                                        state = 5;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_1574_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_1570_,
                                                                        );
                                                                        v___x_1576_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1577_ =
                                                                            v_isSharedCheck_1581_;
                                                                        state = 5;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec(v_a_1566_);
                                                                leanh::lean_dec(v_a_1564_);
                                                                leanh::lean_dec_ref(
                                                                    v_proof_1505_,
                                                                );
                                                                return v___x_1569_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_a_1566_);
                                                            leanh::lean_dec(v_a_1564_);
                                                            leanh::lean_dec(
                                                                v_generation_1506_,
                                                            );
                                                            leanh::lean_dec_ref(
                                                                v_proof_1505_,
                                                            );
                                                            return v___x_1568_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_a_1564_);
                                                        leanh::lean_dec(v_generation_1506_);
                                                        leanh::lean_dec_ref(v_proof_1505_);
                                                        v_a_1582_ = leanh::lean_ctor_get(
                                                            v___x_1565_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1589_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_1565_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1589_ == 0 {
                                                            v___x_1584_ = v___x_1565_;
                                                            v_isShared_1585_ =
                                                                v_isSharedCheck_1589_;
                                                            state = 7;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_1582_);
                                                            leanh::lean_dec(v___x_1565_);
                                                            v___x_1584_ = leanh::lean_box(0);
                                                            v_isShared_1585_ =
                                                                v_isSharedCheck_1589_;
                                                            state = 7;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v_arg_1547_);
                                                    leanh::lean_dec(v_generation_1506_);
                                                    leanh::lean_dec_ref(v_proof_1505_);
                                                    v_a_1590_ =
                                                        leanh::lean_ctor_get(v___x_1563_, 0);
                                                    v_isSharedCheck_1597_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_1563_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1597_ == 0 {
                                                        v___x_1592_ = v___x_1563_;
                                                        v_isShared_1593_ = v_isSharedCheck_1597_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_1590_);
                                                        leanh::lean_dec(v___x_1563_);
                                                        v___x_1592_ = leanh::lean_box(0);
                                                        v_isShared_1593_ = v_isSharedCheck_1597_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_1556_);
                                        leanh::lean_dec_ref(v_arg_1555_);
                                        leanh::lean_dec_ref(v_eqs_1504_);
                                        v___x_1598_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                                            v_arg_1550_,
                                            v_a_1508_,
                                            v_a_1509_,
                                            v_a_1510_,
                                            v_a_1511_,
                                            v_a_1512_,
                                            v_a_1513_,
                                            v_a_1514_,
                                            v_a_1515_,
                                            v_a_1516_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1598_) == 0 {
                                            v_a_1599_ = leanh::lean_ctor_get(v___x_1598_, 0);
                                            leanh::lean_inc(v_a_1599_);
                                            leanh::lean_dec_ref_known(v___x_1598_, 1);
                                            v___x_1600_ =
                                                l_Lean_Meta_Grind_preprocessLight___redArg(
                                                    v_arg_1547_,
                                                    v_a_1508_,
                                                    v_a_1509_,
                                                    v_a_1510_,
                                                    v_a_1511_,
                                                    v_a_1512_,
                                                    v_a_1513_,
                                                    v_a_1514_,
                                                    v_a_1515_,
                                                    v_a_1516_,
                                                );
                                            if leanh::lean_obj_tag(v___x_1600_) == 0 {
                                                v_a_1601_ =
                                                    leanh::lean_ctor_get(v___x_1600_, 0);
                                                leanh::lean_inc(v_a_1601_);
                                                leanh::lean_dec_ref_known(v___x_1600_, 1);
                                                v___x_1602_ = leanh::lean_box(0);
                                                leanh::lean_inc(v_a_1516_);
                                                leanh::lean_inc_ref(v_a_1515_);
                                                leanh::lean_inc(v_a_1514_);
                                                leanh::lean_inc_ref(v_a_1513_);
                                                leanh::lean_inc(v_a_1512_);
                                                leanh::lean_inc_ref(v_a_1511_);
                                                leanh::lean_inc(v_a_1510_);
                                                leanh::lean_inc_ref(v_a_1509_);
                                                leanh::lean_inc(v_a_1508_);
                                                leanh::lean_inc(v_a_1507_);
                                                leanh::lean_inc(v_generation_1506_);
                                                leanh::lean_inc(v_a_1599_);
                                                v___x_1603_ = lean_grind_internalize(
                                                    v_a_1599_,
                                                    v_generation_1506_,
                                                    v___x_1602_,
                                                    v_a_1507_,
                                                    v_a_1508_,
                                                    v_a_1509_,
                                                    v_a_1510_,
                                                    v_a_1511_,
                                                    v_a_1512_,
                                                    v_a_1513_,
                                                    v_a_1514_,
                                                    v_a_1515_,
                                                    v_a_1516_,
                                                );
                                                if leanh::lean_obj_tag(v___x_1603_) == 0 {
                                                    leanh::lean_dec_ref_known(
                                                        v___x_1603_,
                                                        1,
                                                    );
                                                    leanh::lean_inc(v_a_1516_);
                                                    leanh::lean_inc_ref(v_a_1515_);
                                                    leanh::lean_inc(v_a_1514_);
                                                    leanh::lean_inc_ref(v_a_1513_);
                                                    leanh::lean_inc(v_a_1512_);
                                                    leanh::lean_inc_ref(v_a_1511_);
                                                    leanh::lean_inc(v_a_1510_);
                                                    leanh::lean_inc_ref(v_a_1509_);
                                                    leanh::lean_inc(v_a_1508_);
                                                    leanh::lean_inc(v_a_1507_);
                                                    leanh::lean_inc(v_a_1601_);
                                                    v___x_1604_ = lean_grind_internalize(
                                                        v_a_1601_,
                                                        v_generation_1506_,
                                                        v___x_1602_,
                                                        v_a_1507_,
                                                        v_a_1508_,
                                                        v_a_1509_,
                                                        v_a_1510_,
                                                        v_a_1511_,
                                                        v_a_1512_,
                                                        v_a_1513_,
                                                        v_a_1514_,
                                                        v_a_1515_,
                                                        v_a_1516_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_1604_) == 0
                                                    {
                                                        leanh::lean_dec_ref_known(
                                                            v___x_1604_,
                                                            1,
                                                        );
                                                        leanh::lean_inc(v_a_1601_);
                                                        leanh::lean_inc(v_a_1599_);
                                                        v___x_1605_ = l_Lean_Meta_mkEq(
                                                            v_a_1599_, v_a_1601_, v_a_1513_,
                                                            v_a_1514_, v_a_1515_, v_a_1516_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_1605_)
                                                            == 0
                                                        {
                                                            v_a_1606_ = leanh::lean_ctor_get(
                                                                v___x_1605_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_1606_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_1605_,
                                                                1,
                                                            );
                                                            v___x_1607_ =
                                                                l_Lean_Meta_mkExpectedPropHint(
                                                                    v_proof_1505_,
                                                                    v_a_1606_,
                                                                );
                                                            v___x_1608_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1599_, v_a_1601_, v___x_1607_, v___x_1553_, v_a_1507_, v_a_1509_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
                                                            return v___x_1608_;
                                                        } else {
                                                            leanh::lean_dec(v_a_1601_);
                                                            leanh::lean_dec(v_a_1599_);
                                                            leanh::lean_dec_ref(
                                                                v_proof_1505_,
                                                            );
                                                            v_a_1609_ = leanh::lean_ctor_get(
                                                                v___x_1605_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1616_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_1605_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1616_ == 0 {
                                                                v___x_1611_ = v___x_1605_;
                                                                v_isShared_1612_ =
                                                                    v_isSharedCheck_1616_;
                                                                state = 11;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_1609_);
                                                                leanh::lean_dec(v___x_1605_);
                                                                v___x_1611_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_1612_ =
                                                                    v_isSharedCheck_1616_;
                                                                state = 11;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_a_1601_);
                                                        leanh::lean_dec(v_a_1599_);
                                                        leanh::lean_dec_ref(v_proof_1505_);
                                                        return v___x_1604_;
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_a_1601_);
                                                    leanh::lean_dec(v_a_1599_);
                                                    leanh::lean_dec(v_generation_1506_);
                                                    leanh::lean_dec_ref(v_proof_1505_);
                                                    return v___x_1603_;
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_1599_);
                                                leanh::lean_dec(v_generation_1506_);
                                                leanh::lean_dec_ref(v_proof_1505_);
                                                v_a_1617_ =
                                                    leanh::lean_ctor_get(v___x_1600_, 0);
                                                v_isSharedCheck_1624_ =
                                                    (!leanh::lean_is_exclusive(v___x_1600_))
                                                        as u8;
                                                if v_isSharedCheck_1624_ == 0 {
                                                    v___x_1619_ = v___x_1600_;
                                                    v_isShared_1620_ = v_isSharedCheck_1624_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_1617_);
                                                    leanh::lean_dec(v___x_1600_);
                                                    v___x_1619_ = leanh::lean_box(0);
                                                    v_isShared_1620_ = v_isSharedCheck_1624_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_1547_);
                                            leanh::lean_dec(v_generation_1506_);
                                            leanh::lean_dec_ref(v_proof_1505_);
                                            v_a_1625_ = leanh::lean_ctor_get(v___x_1598_, 0);
                                            v_isSharedCheck_1632_ =
                                                (!leanh::lean_is_exclusive(v___x_1598_))
                                                    as u8;
                                            if v_isSharedCheck_1632_ == 0 {
                                                v___x_1627_ = v___x_1598_;
                                                v_isShared_1628_ = v_isSharedCheck_1632_;
                                                state = 15;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1625_);
                                                leanh::lean_dec(v___x_1598_);
                                                v___x_1627_ = leanh::lean_box(0);
                                                v_isShared_1628_ = v_isSharedCheck_1632_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1551_);
                                leanh::lean_dec_ref(v_eqs_1504_);
                                v___x_1633_ = leanh::lean_unsigned_to_nat(0);
                                leanh::lean_inc_ref(v_proof_1505_);
                                v___x_1634_ = l_Lean_Expr_proj___override(
                                    v___x_1552_,
                                    v___x_1633_,
                                    v_proof_1505_,
                                );
                                leanh::lean_inc(v_generation_1506_);
                                v___x_1635_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(v_arg_1550_, v___x_1634_, v_generation_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
                                if leanh::lean_obj_tag(v___x_1635_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1635_, 1);
                                    v___x_1636_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1637_ = l_Lean_Expr_proj___override(
                                        v___x_1552_,
                                        v___x_1636_,
                                        v_proof_1505_,
                                    );
                                    v_eqs_1504_ = v_arg_1547_;
                                    v_proof_1505_ = v___x_1637_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_arg_1547_);
                                    leanh::lean_dec(v_generation_1506_);
                                    leanh::lean_dec_ref(v_proof_1505_);
                                    return v___x_1635_;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_generation_1506_);
                    leanh::lean_dec_ref(v_proof_1505_);
                    leanh::lean_dec_ref(v_eqs_1504_);
                    v_a_1639_ = leanh::lean_ctor_get(v___x_1521_, 0);
                    v_isSharedCheck_1646_ = (!leanh::lean_is_exclusive(v___x_1521_)) as u8;
                    if v_isSharedCheck_1646_ == 0 {
                        v___x_1641_ = v___x_1521_;
                        v_isShared_1642_ = v_isSharedCheck_1646_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1639_);
                        leanh::lean_dec(v___x_1521_);
                        v___x_1641_ = leanh::lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1646_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1519_ = leanh::lean_box(0);
                v___x_1520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                return v___x_1520_;
            }
            2 => {
                v___x_1530_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1524_);
                if leanh::lean_obj_tag(v___x_1530_) == 0 {
                    v_a_1531_ = leanh::lean_ctor_get(v___x_1530_, 0);
                    leanh::lean_inc(v_a_1531_);
                    leanh::lean_dec_ref_known(v___x_1530_, 1);
                    v___x_1532_ = (leanh::lean_unbox(v_a_1531_) as u8);
                    leanh::lean_dec(v_a_1531_);
                    if v___x_1532_ == 0 {
                        leanh::lean_dec_ref(v_eqs_1504_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1533_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1);
                        v___x_1534_ = l_Lean_indentExpr(v_eqs_1504_);
                        v___x_1535_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1535_, 0, v___x_1533_);
                        leanh::lean_ctor_set(v___x_1535_, 1, v___x_1534_);
                        v___x_1536_ = l_Lean_Meta_Sym_reportIssue(
                            v___x_1535_,
                            v___y_1524_,
                            v___y_1525_,
                            v___y_1526_,
                            v___y_1527_,
                            v___y_1528_,
                            v___y_1529_,
                        );
                        if leanh::lean_obj_tag(v___x_1536_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1536_, 1);
                            state = 1;
                            continue;
                        } else {
                            return v___x_1536_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_eqs_1504_);
                    v_a_1537_ = leanh::lean_ctor_get(v___x_1530_, 0);
                    v_isSharedCheck_1544_ = (!leanh::lean_is_exclusive(v___x_1530_)) as u8;
                    if v_isSharedCheck_1544_ == 0 {
                        v___x_1539_ = v___x_1530_;
                        v_isShared_1540_ = v_isSharedCheck_1544_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1537_);
                        leanh::lean_dec(v___x_1530_);
                        v___x_1539_ = leanh::lean_box(0);
                        v_isShared_1540_ = v_isSharedCheck_1544_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1540_ == 0 {
                    v___x_1542_ = v___x_1539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
                    v___x_1542_ = v_reuseFailAlloc_1543_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1542_;
            }
            5 => {
                if v_isShared_1577_ == 0 {
                    v___x_1579_ = v___x_1576_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1579_;
            }
            7 => {
                if v_isShared_1585_ == 0 {
                    v___x_1587_ = v___x_1584_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
                    v___x_1587_ = v_reuseFailAlloc_1588_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1587_;
            }
            9 => {
                if v_isShared_1593_ == 0 {
                    v___x_1595_ = v___x_1592_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
                    v___x_1595_ = v_reuseFailAlloc_1596_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1595_;
            }
            11 => {
                if v_isShared_1612_ == 0 {
                    v___x_1614_ = v___x_1611_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
                    v___x_1614_ = v_reuseFailAlloc_1615_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1614_;
            }
            13 => {
                if v_isShared_1620_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
                    v___x_1622_ = v_reuseFailAlloc_1623_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1622_;
            }
            15 => {
                if v_isShared_1628_ == 0 {
                    v___x_1630_ = v___x_1627_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
                    v___x_1630_ = v_reuseFailAlloc_1631_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1630_;
            }
            17 => {
                if v_isShared_1642_ == 0 {
                    v___x_1644_ = v___x_1641_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
                    v___x_1644_ = v_reuseFailAlloc_1645_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___boxed(
    mut v_eqs_1647_: *mut leanh::LeanObject,
    mut v_proof_1648_: *mut leanh::LeanObject,
    mut v_generation_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_a_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
    mut v_a_1655_: *mut leanh::LeanObject,
    mut v_a_1656_: *mut leanh::LeanObject,
    mut v_a_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
    mut v_a_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1661_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(
        v_eqs_1647_,
        v_proof_1648_,
        v_generation_1649_,
        v_a_1650_,
        v_a_1651_,
        v_a_1652_,
        v_a_1653_,
        v_a_1654_,
        v_a_1655_,
        v_a_1656_,
        v_a_1657_,
        v_a_1658_,
        v_a_1659_,
    );
    leanh::lean_dec(v_a_1659_);
    leanh::lean_dec_ref(v_a_1658_);
    leanh::lean_dec(v_a_1657_);
    leanh::lean_dec_ref(v_a_1656_);
    leanh::lean_dec(v_a_1655_);
    leanh::lean_dec_ref(v_a_1654_);
    leanh::lean_dec(v_a_1653_);
    leanh::lean_dec_ref(v_a_1652_);
    leanh::lean_dec(v_a_1651_);
    leanh::lean_dec(v_a_1650_);
    return v_res_1661_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = lean_st_ref_get(v___y_1666_);
    v_env_1669_ = leanh::lean_ctor_get(v___x_1668_, 0);
    leanh::lean_inc_ref(v_env_1669_);
    leanh::lean_dec(v___x_1668_);
    v___x_1670_ = lean_st_ref_get(v___y_1664_);
    v_mctx_1671_ = leanh::lean_ctor_get(v___x_1670_, 0);
    leanh::lean_inc_ref(v_mctx_1671_);
    leanh::lean_dec(v___x_1670_);
    v_lctx_1672_ = leanh::lean_ctor_get(v___y_1663_, 2);
    v_options_1673_ = leanh::lean_ctor_get(v___y_1665_, 2);
    leanh::lean_inc_ref(v_options_1673_);
    leanh::lean_inc_ref(v_lctx_1672_);
    v___x_1674_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1674_, 0, v_env_1669_);
    leanh::lean_ctor_set(v___x_1674_, 1, v_mctx_1671_);
    leanh::lean_ctor_set(v___x_1674_, 2, v_lctx_1672_);
    leanh::lean_ctor_set(v___x_1674_, 3, v_options_1673_);
    v___x_1675_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    leanh::lean_ctor_set(v___x_1675_, 1, v_msgData_1662_);
    v___x_1676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1676_, 0, v___x_1675_);
    return v___x_1676_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
    mut v___y_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    leanh::lean_dec(v___y_1681_);
    leanh::lean_dec_ref(v___y_1680_);
    leanh::lean_dec(v___y_1679_);
    leanh::lean_dec_ref(v___y_1678_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1690_ = leanh::lean_ctor_get(v___y_1687_, 5);
                v___x_1691_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
                v_a_1692_ = leanh::lean_ctor_get(v___x_1691_, 0);
                v_isSharedCheck_1700_ = (!leanh::lean_is_exclusive(v___x_1691_)) as u8;
                if v_isSharedCheck_1700_ == 0 {
                    v___x_1694_ = v___x_1691_;
                    v_isShared_1695_ = v_isSharedCheck_1700_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1692_);
                    leanh::lean_dec(v___x_1691_);
                    v___x_1694_ = leanh::lean_box(0);
                    v_isShared_1695_ = v_isSharedCheck_1700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1690_);
                v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1696_, 0, v_ref_1690_);
                leanh::lean_ctor_set(v___x_1696_, 1, v_a_1692_);
                if v_isShared_1695_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1694_, 1);
                    leanh::lean_ctor_set(v___x_1694_, 0, v___x_1696_);
                    v___x_1698_ = v___x_1694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
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
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
    leanh::lean_dec(v___y_1705_);
    leanh::lean_dec_ref(v___y_1704_);
    leanh::lean_dec(v___y_1703_);
    leanh::lean_dec_ref(v___y_1702_);
    return v_res_1707_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1708_: *mut leanh::LeanObject,
    mut v_msg_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
    mut v___y_1714_: *mut leanh::LeanObject,
    mut v___y_1715_: *mut leanh::LeanObject,
    mut v___y_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1733_: u8 = 0;
    let mut v_cancelTk_x3f_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1735_: u8 = 0;
    let mut v_inheritedTraceOptions_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1721_ = leanh::lean_ctor_get(v___y_1718_, 0);
    v_fileMap_1722_ = leanh::lean_ctor_get(v___y_1718_, 1);
    v_options_1723_ = leanh::lean_ctor_get(v___y_1718_, 2);
    v_currRecDepth_1724_ = leanh::lean_ctor_get(v___y_1718_, 3);
    v_maxRecDepth_1725_ = leanh::lean_ctor_get(v___y_1718_, 4);
    v_ref_1726_ = leanh::lean_ctor_get(v___y_1718_, 5);
    v_currNamespace_1727_ = leanh::lean_ctor_get(v___y_1718_, 6);
    v_openDecls_1728_ = leanh::lean_ctor_get(v___y_1718_, 7);
    v_initHeartbeats_1729_ = leanh::lean_ctor_get(v___y_1718_, 8);
    v_maxHeartbeats_1730_ = leanh::lean_ctor_get(v___y_1718_, 9);
    v_quotContext_1731_ = leanh::lean_ctor_get(v___y_1718_, 10);
    v_currMacroScope_1732_ = leanh::lean_ctor_get(v___y_1718_, 11);
    v_diag_1733_ = leanh::lean_ctor_get_uint8(
        v___y_1718_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1734_ = leanh::lean_ctor_get(v___y_1718_, 12);
    v_suppressElabErrors_1735_ = leanh::lean_ctor_get_uint8(
        v___y_1718_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1736_ = leanh::lean_ctor_get(v___y_1718_, 13);
    v_ref_1737_ = l_Lean_replaceRef(v_ref_1708_, v_ref_1726_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1736_);
    leanh::lean_inc(v_cancelTk_x3f_1734_);
    leanh::lean_inc(v_currMacroScope_1732_);
    leanh::lean_inc(v_quotContext_1731_);
    leanh::lean_inc(v_maxHeartbeats_1730_);
    leanh::lean_inc(v_initHeartbeats_1729_);
    leanh::lean_inc(v_openDecls_1728_);
    leanh::lean_inc(v_currNamespace_1727_);
    leanh::lean_inc(v_maxRecDepth_1725_);
    leanh::lean_inc(v_currRecDepth_1724_);
    leanh::lean_inc_ref(v_options_1723_);
    leanh::lean_inc_ref(v_fileMap_1722_);
    leanh::lean_inc_ref(v_fileName_1721_);
    v___x_1738_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1738_, 0, v_fileName_1721_);
    leanh::lean_ctor_set(v___x_1738_, 1, v_fileMap_1722_);
    leanh::lean_ctor_set(v___x_1738_, 2, v_options_1723_);
    leanh::lean_ctor_set(v___x_1738_, 3, v_currRecDepth_1724_);
    leanh::lean_ctor_set(v___x_1738_, 4, v_maxRecDepth_1725_);
    leanh::lean_ctor_set(v___x_1738_, 5, v_ref_1737_);
    leanh::lean_ctor_set(v___x_1738_, 6, v_currNamespace_1727_);
    leanh::lean_ctor_set(v___x_1738_, 7, v_openDecls_1728_);
    leanh::lean_ctor_set(v___x_1738_, 8, v_initHeartbeats_1729_);
    leanh::lean_ctor_set(v___x_1738_, 9, v_maxHeartbeats_1730_);
    leanh::lean_ctor_set(v___x_1738_, 10, v_quotContext_1731_);
    leanh::lean_ctor_set(v___x_1738_, 11, v_currMacroScope_1732_);
    leanh::lean_ctor_set(v___x_1738_, 12, v_cancelTk_x3f_1734_);
    leanh::lean_ctor_set(v___x_1738_, 13, v_inheritedTraceOptions_1736_);
    leanh::lean_ctor_set_uint8(
        v___x_1738_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1733_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1738_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1735_,
    );
    v___x_1739_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1709_, v___y_1716_, v___y_1717_, v___x_1738_, v___y_1719_);
    leanh::lean_dec_ref_known(v___x_1738_, 14);
    return v___x_1739_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1740_: *mut leanh::LeanObject,
    mut v_msg_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
    mut v___y_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
    mut v___y_1747_: *mut leanh::LeanObject,
    mut v___y_1748_: *mut leanh::LeanObject,
    mut v___y_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1740_, v_msg_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
    leanh::lean_dec(v___y_1751_);
    leanh::lean_dec_ref(v___y_1750_);
    leanh::lean_dec(v___y_1749_);
    leanh::lean_dec_ref(v___y_1748_);
    leanh::lean_dec(v___y_1747_);
    leanh::lean_dec_ref(v___y_1746_);
    leanh::lean_dec(v___y_1745_);
    leanh::lean_dec_ref(v___y_1744_);
    leanh::lean_dec(v___y_1743_);
    leanh::lean_dec(v___y_1742_);
    leanh::lean_dec(v_ref_1740_);
    return v_res_1753_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_1756_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1758_ = leanh::lean_unsigned_to_nat(0);
    v___x_1759_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    leanh::lean_ctor_set(v___x_1759_, 1, v___x_1758_);
    leanh::lean_ctor_set(v___x_1759_, 2, v___x_1758_);
    leanh::lean_ctor_set(v___x_1759_, 3, v___x_1758_);
    leanh::lean_ctor_set(v___x_1759_, 4, v___x_1757_);
    leanh::lean_ctor_set(v___x_1759_, 5, v___x_1757_);
    leanh::lean_ctor_set(v___x_1759_, 6, v___x_1757_);
    leanh::lean_ctor_set(v___x_1759_, 7, v___x_1757_);
    leanh::lean_ctor_set(v___x_1759_, 8, v___x_1757_);
    leanh::lean_ctor_set(v___x_1759_, 9, v___x_1757_);
    return v___x_1759_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = leanh::lean_unsigned_to_nat(32);
    v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1760_);
    v___x_1762_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1761_);
    return v___x_1762_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1763_: usize = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = 5usize;
    v___x_1764_ = leanh::lean_unsigned_to_nat(0);
    v___x_1765_ = leanh::lean_unsigned_to_nat(32);
    v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
    v___x_1767_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_1768_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1768_, 0, v___x_1767_);
    leanh::lean_ctor_set(v___x_1768_, 1, v___x_1766_);
    leanh::lean_ctor_set(v___x_1768_, 2, v___x_1764_);
    leanh::lean_ctor_set(v___x_1768_, 3, v___x_1764_);
    leanh::lean_ctor_set_usize(v___x_1768_, 4, v___x_1763_);
    return v___x_1768_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ = leanh::lean_box(1);
    v___x_1770_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1771_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1772_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    leanh::lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    leanh::lean_ctor_set(v___x_1772_, 2, v___x_1769_);
    return v___x_1772_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
    return v___x_1781_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
    return v___x_1784_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
    return v___x_1787_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
    return v___x_1790_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1794_: *mut leanh::LeanObject,
    mut v_declHint_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut v_isExporting_1801_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1798_ = lean_st_ref_get(v___y_1796_);
                v_env_1799_ = leanh::lean_ctor_get(v___x_1798_, 0);
                leanh::lean_inc_ref(v_env_1799_);
                leanh::lean_dec(v___x_1798_);
                v___x_1800_ = l_Lean_Name_isAnonymous(v_declHint_1795_);
                if v___x_1800_ == 0 {
                    v_isExporting_1801_ = leanh::lean_ctor_get_uint8(
                        v_env_1799_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1801_ == 0 {
                        leanh::lean_dec_ref(v_env_1799_);
                        leanh::lean_dec(v_declHint_1795_);
                        v___x_1802_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1802_, 0, v_msg_1794_);
                        return v___x_1802_;
                    } else {
                        leanh::lean_inc_ref(v_env_1799_);
                        v___x_1803_ = l_Lean_Environment_setExporting(v_env_1799_, v___x_1800_);
                        leanh::lean_inc(v_declHint_1795_);
                        leanh::lean_inc_ref(v___x_1803_);
                        v___x_1804_ = l_Lean_Environment_contains(
                            v___x_1803_,
                            v_declHint_1795_,
                            v_isExporting_1801_,
                        );
                        if v___x_1804_ == 0 {
                            leanh::lean_dec_ref(v___x_1803_);
                            leanh::lean_dec_ref(v_env_1799_);
                            leanh::lean_dec(v_declHint_1795_);
                            v___x_1805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1805_, 0, v_msg_1794_);
                            return v___x_1805_;
                        } else {
                            v___x_1806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1807_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1808_ = l_Lean_Options_empty;
                            v___x_1809_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1809_, 0, v___x_1803_);
                            leanh::lean_ctor_set(v___x_1809_, 1, v___x_1806_);
                            leanh::lean_ctor_set(v___x_1809_, 2, v___x_1807_);
                            leanh::lean_ctor_set(v___x_1809_, 3, v___x_1808_);
                            leanh::lean_inc(v_declHint_1795_);
                            v___x_1810_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1795_, v___x_1800_);
                            v_c_1811_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1811_, 0, v___x_1809_);
                            leanh::lean_ctor_set(v_c_1811_, 1, v___x_1810_);
                            v___x_1812_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1799_,
                                v_declHint_1795_,
                            );
                            if leanh::lean_obj_tag(v___x_1812_) == 0 {
                                leanh::lean_dec_ref(v_env_1799_);
                                leanh::lean_dec(v_declHint_1795_);
                                v___x_1813_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1814_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1814_, 0, v___x_1813_);
                                leanh::lean_ctor_set(v___x_1814_, 1, v_c_1811_);
                                v___x_1815_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1816_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1816_, 0, v___x_1814_);
                                leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
                                v___x_1817_ = l_Lean_MessageData_note(v___x_1816_);
                                v___x_1818_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1818_, 0, v_msg_1794_);
                                leanh::lean_ctor_set(v___x_1818_, 1, v___x_1817_);
                                v___x_1819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
                                return v___x_1819_;
                            } else {
                                v_val_1820_ = leanh::lean_ctor_get(v___x_1812_, 0);
                                v_isSharedCheck_1855_ =
                                    (!leanh::lean_is_exclusive(v___x_1812_)) as u8;
                                if v_isSharedCheck_1855_ == 0 {
                                    v___x_1822_ = v___x_1812_;
                                    v_isShared_1823_ = v_isSharedCheck_1855_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1820_);
                                    leanh::lean_dec(v___x_1812_);
                                    v___x_1822_ = leanh::lean_box(0);
                                    v_isShared_1823_ = v_isSharedCheck_1855_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1799_);
                    leanh::lean_dec(v_declHint_1795_);
                    v___x_1856_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1856_, 0, v_msg_1794_);
                    return v___x_1856_;
                }
            }
            1 => {
                v___x_1824_ = leanh::lean_box(0);
                v___x_1825_ = l_Lean_Environment_header(v_env_1799_);
                leanh::lean_dec_ref(v_env_1799_);
                v___x_1826_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1825_);
                v_mod_1827_ = lean_array_get(v___x_1824_, v___x_1826_, v_val_1820_);
                leanh::lean_dec(v_val_1820_);
                leanh::lean_dec_ref(v___x_1826_);
                v___x_1828_ = l_Lean_isPrivateName(v_declHint_1795_);
                leanh::lean_dec(v_declHint_1795_);
                if v___x_1828_ == 0 {
                    v___x_1829_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1830_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1830_, 0, v___x_1829_);
                    leanh::lean_ctor_set(v___x_1830_, 1, v_c_1811_);
                    v___x_1831_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1832_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1832_, 0, v___x_1830_);
                    leanh::lean_ctor_set(v___x_1832_, 1, v___x_1831_);
                    v___x_1833_ = l_Lean_MessageData_ofName(v_mod_1827_);
                    v___x_1834_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1834_, 0, v___x_1832_);
                    leanh::lean_ctor_set(v___x_1834_, 1, v___x_1833_);
                    v___x_1835_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1836_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1836_, 0, v___x_1834_);
                    leanh::lean_ctor_set(v___x_1836_, 1, v___x_1835_);
                    v___x_1837_ = l_Lean_MessageData_note(v___x_1836_);
                    v___x_1838_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1838_, 0, v_msg_1794_);
                    leanh::lean_ctor_set(v___x_1838_, 1, v___x_1837_);
                    if v_isShared_1823_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1822_, 0);
                        leanh::lean_ctor_set(v___x_1822_, 0, v___x_1838_);
                        v___x_1840_ = v___x_1822_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
                        v___x_1840_ = v_reuseFailAlloc_1841_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1842_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1843_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1843_, 0, v___x_1842_);
                    leanh::lean_ctor_set(v___x_1843_, 1, v_c_1811_);
                    v___x_1844_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1845_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1845_, 0, v___x_1843_);
                    leanh::lean_ctor_set(v___x_1845_, 1, v___x_1844_);
                    v___x_1846_ = l_Lean_MessageData_ofName(v_mod_1827_);
                    v___x_1847_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1847_, 0, v___x_1845_);
                    leanh::lean_ctor_set(v___x_1847_, 1, v___x_1846_);
                    v___x_1848_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1849_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1849_, 0, v___x_1847_);
                    leanh::lean_ctor_set(v___x_1849_, 1, v___x_1848_);
                    v___x_1850_ = l_Lean_MessageData_note(v___x_1849_);
                    v___x_1851_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1851_, 0, v_msg_1794_);
                    leanh::lean_ctor_set(v___x_1851_, 1, v___x_1850_);
                    if v_isShared_1823_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1822_, 0);
                        leanh::lean_ctor_set(v___x_1822_, 0, v___x_1851_);
                        v___x_1853_ = v___x_1822_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1854_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
                        v___x_1853_ = v_reuseFailAlloc_1854_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1840_;
            }
            3 => {
                return v___x_1853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_1857_: *mut leanh::LeanObject,
    mut v_declHint_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1857_, v_declHint_1858_, v___y_1859_);
    leanh::lean_dec(v___y_1859_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1862_: *mut leanh::LeanObject,
    mut v_declHint_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
    mut v___y_1872_: *mut leanh::LeanObject,
    mut v___y_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1862_, v_declHint_1863_, v___y_1873_);
                v_a_1876_ = leanh::lean_ctor_get(v___x_1875_, 0);
                v_isSharedCheck_1885_ = (!leanh::lean_is_exclusive(v___x_1875_)) as u8;
                if v_isSharedCheck_1885_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    v_isShared_1879_ = v_isSharedCheck_1885_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1876_);
                    leanh::lean_dec(v___x_1875_);
                    v___x_1878_ = leanh::lean_box(0);
                    v_isShared_1879_ = v_isSharedCheck_1885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1880_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1881_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1881_, 0, v___x_1880_);
                leanh::lean_ctor_set(v___x_1881_, 1, v_a_1876_);
                if v_isShared_1879_ == 0 {
                    leanh::lean_ctor_set(v___x_1878_, 0, v___x_1881_);
                    v___x_1883_ = v___x_1878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_1886_: *mut leanh::LeanObject,
    mut v_declHint_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
    mut v___y_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1886_, v_declHint_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
    leanh::lean_dec(v___y_1897_);
    leanh::lean_dec_ref(v___y_1896_);
    leanh::lean_dec(v___y_1895_);
    leanh::lean_dec_ref(v___y_1894_);
    leanh::lean_dec(v___y_1893_);
    leanh::lean_dec_ref(v___y_1892_);
    leanh::lean_dec(v___y_1891_);
    leanh::lean_dec_ref(v___y_1890_);
    leanh::lean_dec(v___y_1889_);
    leanh::lean_dec(v___y_1888_);
    return v_res_1899_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1900_: *mut leanh::LeanObject,
    mut v_msg_1901_: *mut leanh::LeanObject,
    mut v_declHint_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
    mut v___y_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1901_, v_declHint_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    v_a_1915_ = leanh::lean_ctor_get(v___x_1914_, 0);
    leanh::lean_inc(v_a_1915_);
    leanh::lean_dec_ref(v___x_1914_);
    v___x_1916_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1900_, v_a_1915_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1917_: *mut leanh::LeanObject,
    mut v_msg_1918_: *mut leanh::LeanObject,
    mut v_declHint_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1931_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1917_, v_msg_1918_, v_declHint_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
    leanh::lean_dec(v___y_1929_);
    leanh::lean_dec_ref(v___y_1928_);
    leanh::lean_dec(v___y_1927_);
    leanh::lean_dec_ref(v___y_1926_);
    leanh::lean_dec(v___y_1925_);
    leanh::lean_dec_ref(v___y_1924_);
    leanh::lean_dec(v___y_1923_);
    leanh::lean_dec_ref(v___y_1922_);
    leanh::lean_dec(v___y_1921_);
    leanh::lean_dec(v___y_1920_);
    leanh::lean_dec(v_ref_1917_);
    return v_res_1931_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1938_: *mut leanh::LeanObject,
    mut v_constName_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
    mut v___y_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1951_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1952_ = 0;
    leanh::lean_inc(v_constName_1939_);
    v___x_1953_ = l_Lean_MessageData_ofConstName(v_constName_1939_, v___x_1952_);
    v___x_1954_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1954_, 0, v___x_1951_);
    leanh::lean_ctor_set(v___x_1954_, 1, v___x_1953_);
    v___x_1955_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1956_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1956_, 0, v___x_1954_);
    leanh::lean_ctor_set(v___x_1956_, 1, v___x_1955_);
    v___x_1957_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1938_, v___x_1956_, v_constName_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1958_: *mut leanh::LeanObject,
    mut v_constName_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
    mut v___y_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(v_ref_1958_, v_constName_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
    leanh::lean_dec(v___y_1969_);
    leanh::lean_dec_ref(v___y_1968_);
    leanh::lean_dec(v___y_1967_);
    leanh::lean_dec_ref(v___y_1966_);
    leanh::lean_dec(v___y_1965_);
    leanh::lean_dec_ref(v___y_1964_);
    leanh::lean_dec(v___y_1963_);
    leanh::lean_dec_ref(v___y_1962_);
    leanh::lean_dec(v___y_1961_);
    leanh::lean_dec(v___y_1960_);
    leanh::lean_dec(v_ref_1958_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(
    mut v_constName_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v___y_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1984_ = leanh::lean_ctor_get(v___y_1981_, 5);
    v___x_1985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(v_ref_1984_, v_constName_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
    return v___x_1985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg___boxed(
    mut v_constName_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(v_constName_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
    leanh::lean_dec(v___y_1996_);
    leanh::lean_dec_ref(v___y_1995_);
    leanh::lean_dec(v___y_1994_);
    leanh::lean_dec_ref(v___y_1993_);
    leanh::lean_dec(v___y_1992_);
    leanh::lean_dec_ref(v___y_1991_);
    leanh::lean_dec(v___y_1990_);
    leanh::lean_dec_ref(v___y_1989_);
    leanh::lean_dec(v___y_1988_);
    leanh::lean_dec(v___y_1987_);
    return v_res_1998_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(
    mut v_constName_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = lean_st_ref_get(v___y_2009_);
                v_env_2012_ = leanh::lean_ctor_get(v___x_2011_, 0);
                leanh::lean_inc_ref(v_env_2012_);
                leanh::lean_dec(v___x_2011_);
                v___x_2013_ = 0;
                leanh::lean_inc(v_constName_1999_);
                v___x_2014_ =
                    l_Lean_Environment_find_x3f(v_env_2012_, v_constName_1999_, v___x_2013_);
                if leanh::lean_obj_tag(v___x_2014_) == 0 {
                    v___x_2015_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(v_constName_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
                    return v___x_2015_;
                } else {
                    leanh::lean_dec(v_constName_1999_);
                    v_val_2016_ = leanh::lean_ctor_get(v___x_2014_, 0);
                    v_isSharedCheck_2023_ = (!leanh::lean_is_exclusive(v___x_2014_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v___x_2018_ = v___x_2014_;
                        v_isShared_2019_ = v_isSharedCheck_2023_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2016_);
                        leanh::lean_dec(v___x_2014_);
                        v___x_2018_ = leanh::lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2019_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2018_, 0);
                    v___x_2021_ = v___x_2018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_val_2016_);
                    v___x_2021_ = v_reuseFailAlloc_2022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0___boxed(
    mut v_constName_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
    mut v___y_2030_: *mut leanh::LeanObject,
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
    mut v___y_2034_: *mut leanh::LeanObject,
    mut v___y_2035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
    leanh::lean_dec(v___y_2034_);
    leanh::lean_dec_ref(v___y_2033_);
    leanh::lean_dec(v___y_2032_);
    leanh::lean_dec_ref(v___y_2031_);
    leanh::lean_dec(v___y_2030_);
    leanh::lean_dec_ref(v___y_2029_);
    leanh::lean_dec(v___y_2028_);
    leanh::lean_dec_ref(v___y_2027_);
    leanh::lean_dec(v___y_2026_);
    leanh::lean_dec(v___y_2025_);
    return v_res_2036_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1()
-> u64 {
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: u64 = 0;
    v___x_2038_ = 1;
    v___x_2039_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2038_);
    return v___x_2039_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo(
    mut v_00_u03b1_2040_: *mut leanh::LeanObject,
    mut v_a_2041_: *mut leanh::LeanObject,
    mut v_b_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
    mut v_a_2047_: *mut leanh::LeanObject,
    mut v_a_2048_: *mut leanh::LeanObject,
    mut v_a_2049_: *mut leanh::LeanObject,
    mut v_a_2050_: *mut leanh::LeanObject,
    mut v_a_2051_: *mut leanh::LeanObject,
    mut v_a_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_a_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_a_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_ctor_u2081_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctor_u2082_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noConfusionDeclName_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: u8 = 0;
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_a_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2120_: u8 = 0;
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_a_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_injDeclName_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2151_: u8 = 0;
    let mut v_ctxApprox_2152_: u8 = 0;
    let mut v_quasiPatternApprox_2153_: u8 = 0;
    let mut v_constApprox_2154_: u8 = 0;
    let mut v_isDefEqStuckEx_2155_: u8 = 0;
    let mut v_unificationHints_2156_: u8 = 0;
    let mut v_proofIrrelevance_2157_: u8 = 0;
    let mut v_assignSyntheticOpaque_2158_: u8 = 0;
    let mut v_offsetCnstrs_2159_: u8 = 0;
    let mut v_etaStruct_2160_: u8 = 0;
    let mut v_univApprox_2161_: u8 = 0;
    let mut v_iota_2162_: u8 = 0;
    let mut v_beta_2163_: u8 = 0;
    let mut v_proj_2164_: u8 = 0;
    let mut v_zeta_2165_: u8 = 0;
    let mut v_zetaDelta_2166_: u8 = 0;
    let mut v_zetaUnused_2167_: u8 = 0;
    let mut v_zetaHave_2168_: u8 = 0;
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v_trackZetaDelta_2172_: u8 = 0;
    let mut v_zetaDeltaSet_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2179_: u8 = 0;
    let mut v_inTypeClassResolution_2180_: u8 = 0;
    let mut v_cacheInferType_2181_: u8 = 0;
    let mut v___x_2182_: u8 = 0;
    let mut v_config_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u64 = 0;
    let mut v___x_2186_: u64 = 0;
    let mut v___x_2187_: u64 = 0;
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u64 = 0;
    let mut v___x_2197_: u64 = 0;
    let mut v_key_2198_: u64 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2207_: u8 = 0;
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_reuseFailAlloc_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut v_a_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2221_: u8 = 0;
    let mut v_a_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v_a_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ctor_u2081_2089_ = l_Lean_Expr_getAppFn(v_a_2041_);
                v_ctor_u2082_2090_ = l_Lean_Expr_getAppFn(v_b_2042_);
                v___x_2091_ = lean_expr_eqv(v_ctor_u2081_2089_, v_ctor_u2082_2090_);
                leanh::lean_dec_ref(v_ctor_u2082_2090_);
                v___x_2092_ = 1;
                if v___x_2091_ == 0 {
                    leanh::lean_dec_ref(v_ctor_u2081_2089_);
                    v___x_2093_ = l_Lean_Expr_getAppFn(v_00_u03b1_2040_);
                    if leanh::lean_obj_tag(v___x_2093_) == 4 {
                        v_declName_2094_ = leanh::lean_ctor_get(v___x_2093_, 0);
                        leanh::lean_inc(v_declName_2094_);
                        leanh::lean_dec_ref_known(v___x_2093_, 2);
                        v___x_2095_ = lean_st_ref_get(v_a_2052_);
                        v_env_2096_ = leanh::lean_ctor_get(v___x_2095_, 0);
                        leanh::lean_inc_ref(v_env_2096_);
                        leanh::lean_dec(v___x_2095_);
                        v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0;
                        v_noConfusionDeclName_2098_ =
                            l_Lean_Name_str___override(v_declName_2094_, v___x_2097_);
                        v___x_2099_ = l_Lean_Environment_contains(
                            v_env_2096_,
                            v_noConfusionDeclName_2098_,
                            v___x_2092_,
                        );
                        if v___x_2099_ == 0 {
                            leanh::lean_dec_ref(v_b_2042_);
                            leanh::lean_dec_ref(v_a_2041_);
                            v___x_2100_ = leanh::lean_box(0);
                            v___x_2101_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2101_, 0, v___x_2100_);
                            return v___x_2101_;
                        } else {
                            v___x_2102_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2047_);
                            if leanh::lean_obj_tag(v___x_2102_) == 0 {
                                v_a_2103_ = leanh::lean_ctor_get(v___x_2102_, 0);
                                leanh::lean_inc(v_a_2103_);
                                leanh::lean_dec_ref_known(v___x_2102_, 1);
                                leanh::lean_inc(v_a_2052_);
                                leanh::lean_inc_ref(v_a_2051_);
                                leanh::lean_inc(v_a_2050_);
                                leanh::lean_inc_ref(v_a_2049_);
                                leanh::lean_inc(v_a_2048_);
                                leanh::lean_inc_ref(v_a_2047_);
                                leanh::lean_inc(v_a_2046_);
                                leanh::lean_inc_ref(v_a_2045_);
                                leanh::lean_inc(v_a_2044_);
                                leanh::lean_inc(v_a_2043_);
                                v___x_2104_ = lean_grind_mk_eq_proof(
                                    v_a_2041_, v_b_2042_, v_a_2043_, v_a_2044_, v_a_2045_,
                                    v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_,
                                    v_a_2051_, v_a_2052_,
                                );
                                if leanh::lean_obj_tag(v___x_2104_) == 0 {
                                    v_a_2105_ = leanh::lean_ctor_get(v___x_2104_, 0);
                                    leanh::lean_inc(v_a_2105_);
                                    leanh::lean_dec_ref_known(v___x_2104_, 1);
                                    v___x_2106_ = l_Lean_Meta_mkNoConfusion(
                                        v_a_2103_, v_a_2105_, v_a_2049_, v_a_2050_, v_a_2051_,
                                        v_a_2052_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2106_) == 0 {
                                        v_a_2107_ = leanh::lean_ctor_get(v___x_2106_, 0);
                                        leanh::lean_inc(v_a_2107_);
                                        leanh::lean_dec_ref_known(v___x_2106_, 1);
                                        v___x_2108_ = l_Lean_Meta_Grind_closeGoal(
                                            v_a_2107_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_,
                                            v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_,
                                            v_a_2052_,
                                        );
                                        return v___x_2108_;
                                    } else {
                                        v_a_2109_ = leanh::lean_ctor_get(v___x_2106_, 0);
                                        v_isSharedCheck_2116_ =
                                            (!leanh::lean_is_exclusive(v___x_2106_)) as u8;
                                        if v_isSharedCheck_2116_ == 0 {
                                            v___x_2111_ = v___x_2106_;
                                            v_isShared_2112_ = v_isSharedCheck_2116_;
                                            state = 8;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2109_);
                                            leanh::lean_dec(v___x_2106_);
                                            v___x_2111_ = leanh::lean_box(0);
                                            v_isShared_2112_ = v_isSharedCheck_2116_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2103_);
                                    v_a_2117_ = leanh::lean_ctor_get(v___x_2104_, 0);
                                    v_isSharedCheck_2124_ =
                                        (!leanh::lean_is_exclusive(v___x_2104_)) as u8;
                                    if v_isSharedCheck_2124_ == 0 {
                                        v___x_2119_ = v___x_2104_;
                                        v_isShared_2120_ = v_isSharedCheck_2124_;
                                        state = 10;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2117_);
                                        leanh::lean_dec(v___x_2104_);
                                        v___x_2119_ = leanh::lean_box(0);
                                        v_isShared_2120_ = v_isSharedCheck_2124_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_2042_);
                                leanh::lean_dec_ref(v_a_2041_);
                                v_a_2125_ = leanh::lean_ctor_get(v___x_2102_, 0);
                                v_isSharedCheck_2132_ =
                                    (!leanh::lean_is_exclusive(v___x_2102_)) as u8;
                                if v_isSharedCheck_2132_ == 0 {
                                    v___x_2127_ = v___x_2102_;
                                    v_isShared_2128_ = v_isSharedCheck_2132_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2125_);
                                    leanh::lean_dec(v___x_2102_);
                                    v___x_2127_ = leanh::lean_box(0);
                                    v_isShared_2128_ = v_isSharedCheck_2132_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2093_);
                        leanh::lean_dec_ref(v_b_2042_);
                        leanh::lean_dec_ref(v_a_2041_);
                        v___x_2133_ = leanh::lean_box(0);
                        v___x_2134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2134_, 0, v___x_2133_);
                        return v___x_2134_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_ctor_u2081_2089_) == 4 {
                        v_declName_2135_ = leanh::lean_ctor_get(v_ctor_u2081_2089_, 0);
                        leanh::lean_inc(v_declName_2135_);
                        leanh::lean_dec_ref_known(v_ctor_u2081_2089_, 2);
                        v___x_2136_ = lean_st_ref_get(v_a_2052_);
                        v_env_2137_ = leanh::lean_ctor_get(v___x_2136_, 0);
                        leanh::lean_inc_ref(v_env_2137_);
                        leanh::lean_dec(v___x_2136_);
                        v_injDeclName_2138_ =
                            l_Lean_Meta_mkInjectiveTheoremNameFor(v_declName_2135_);
                        leanh::lean_inc(v_injDeclName_2138_);
                        v___x_2139_ = l_Lean_Environment_contains(
                            v_env_2137_,
                            v_injDeclName_2138_,
                            v___x_2092_,
                        );
                        if v___x_2139_ == 0 {
                            leanh::lean_dec(v_injDeclName_2138_);
                            leanh::lean_dec_ref(v_b_2042_);
                            leanh::lean_dec_ref(v_a_2041_);
                            v___x_2140_ = leanh::lean_box(0);
                            v___x_2141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2141_, 0, v___x_2140_);
                            return v___x_2141_;
                        } else {
                            leanh::lean_inc(v_injDeclName_2138_);
                            v___x_2142_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_injDeclName_2138_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                            if leanh::lean_obj_tag(v___x_2142_) == 0 {
                                v_a_2143_ = leanh::lean_ctor_get(v___x_2142_, 0);
                                leanh::lean_inc(v_a_2143_);
                                leanh::lean_dec_ref_known(v___x_2142_, 1);
                                leanh::lean_inc(v_a_2052_);
                                leanh::lean_inc_ref(v_a_2051_);
                                leanh::lean_inc(v_a_2050_);
                                leanh::lean_inc_ref(v_a_2049_);
                                leanh::lean_inc(v_a_2048_);
                                leanh::lean_inc_ref(v_a_2047_);
                                leanh::lean_inc(v_a_2046_);
                                leanh::lean_inc_ref(v_a_2045_);
                                leanh::lean_inc(v_a_2044_);
                                leanh::lean_inc(v_a_2043_);
                                leanh::lean_inc_ref(v_b_2042_);
                                leanh::lean_inc_ref(v_a_2041_);
                                v___x_2144_ = lean_grind_mk_eq_proof(
                                    v_a_2041_, v_b_2042_, v_a_2043_, v_a_2044_, v_a_2045_,
                                    v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_,
                                    v_a_2051_, v_a_2052_,
                                );
                                if leanh::lean_obj_tag(v___x_2144_) == 0 {
                                    v_a_2145_ = leanh::lean_ctor_get(v___x_2144_, 0);
                                    leanh::lean_inc(v_a_2145_);
                                    leanh::lean_dec_ref_known(v___x_2144_, 1);
                                    leanh::lean_inc_ref(v_b_2042_);
                                    leanh::lean_inc_ref(v_a_2041_);
                                    v___x_2146_ = l_Lean_Meta_mkEq(
                                        v_a_2041_, v_b_2042_, v_a_2049_, v_a_2050_, v_a_2051_,
                                        v_a_2052_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2146_) == 0 {
                                        v_a_2147_ = leanh::lean_ctor_get(v___x_2146_, 0);
                                        leanh::lean_inc(v_a_2147_);
                                        leanh::lean_dec_ref_known(v___x_2146_, 1);
                                        v___x_2148_ = l_Lean_Meta_mkExpectedTypeHint(
                                            v_a_2145_, v_a_2147_, v_a_2049_, v_a_2050_, v_a_2051_,
                                            v_a_2052_,
                                        );
                                        if leanh::lean_obj_tag(v___x_2148_) == 0 {
                                            v_a_2149_ = leanh::lean_ctor_get(v___x_2148_, 0);
                                            leanh::lean_inc(v_a_2149_);
                                            leanh::lean_dec_ref_known(v___x_2148_, 1);
                                            v___x_2150_ = l_Lean_Meta_Context_config(v_a_2049_);
                                            v_foApprox_2151_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                0 as u32,
                                            );
                                            v_ctxApprox_2152_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                1 as u32,
                                            );
                                            v_quasiPatternApprox_2153_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    2 as u32,
                                                );
                                            v_constApprox_2154_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                3 as u32,
                                            );
                                            v_isDefEqStuckEx_2155_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    4 as u32,
                                                );
                                            v_unificationHints_2156_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    5 as u32,
                                                );
                                            v_proofIrrelevance_2157_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    6 as u32,
                                                );
                                            v_assignSyntheticOpaque_2158_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    7 as u32,
                                                );
                                            v_offsetCnstrs_2159_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    8 as u32,
                                                );
                                            v_etaStruct_2160_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                10 as u32,
                                            );
                                            v_univApprox_2161_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                11 as u32,
                                            );
                                            v_iota_2162_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                12 as u32,
                                            );
                                            v_beta_2163_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                13 as u32,
                                            );
                                            v_proj_2164_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                14 as u32,
                                            );
                                            v_zeta_2165_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                15 as u32,
                                            );
                                            v_zetaDelta_2166_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                16 as u32,
                                            );
                                            v_zetaUnused_2167_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                17 as u32,
                                            );
                                            v_zetaHave_2168_ = leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                18 as u32,
                                            );
                                            v_isSharedCheck_2213_ =
                                                (!leanh::lean_is_exclusive(v___x_2150_))
                                                    as u8;
                                            if v_isSharedCheck_2213_ == 0 {
                                                v___x_2170_ = v___x_2150_;
                                                v_isShared_2171_ = v_isSharedCheck_2213_;
                                                state = 14;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___x_2150_);
                                                v___x_2170_ = leanh::lean_box(0);
                                                v_isShared_2171_ = v_isSharedCheck_2213_;
                                                state = 14;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_2143_);
                                            leanh::lean_dec(v_injDeclName_2138_);
                                            leanh::lean_dec_ref(v_b_2042_);
                                            leanh::lean_dec_ref(v_a_2041_);
                                            v_a_2214_ = leanh::lean_ctor_get(v___x_2148_, 0);
                                            v_isSharedCheck_2221_ =
                                                (!leanh::lean_is_exclusive(v___x_2148_))
                                                    as u8;
                                            if v_isSharedCheck_2221_ == 0 {
                                                v___x_2216_ = v___x_2148_;
                                                v_isShared_2217_ = v_isSharedCheck_2221_;
                                                state = 18;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2214_);
                                                leanh::lean_dec(v___x_2148_);
                                                v___x_2216_ = leanh::lean_box(0);
                                                v_isShared_2217_ = v_isSharedCheck_2221_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_2145_);
                                        leanh::lean_dec(v_a_2143_);
                                        leanh::lean_dec(v_injDeclName_2138_);
                                        leanh::lean_dec_ref(v_b_2042_);
                                        leanh::lean_dec_ref(v_a_2041_);
                                        v_a_2222_ = leanh::lean_ctor_get(v___x_2146_, 0);
                                        v_isSharedCheck_2229_ =
                                            (!leanh::lean_is_exclusive(v___x_2146_)) as u8;
                                        if v_isSharedCheck_2229_ == 0 {
                                            v___x_2224_ = v___x_2146_;
                                            v_isShared_2225_ = v_isSharedCheck_2229_;
                                            state = 20;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2222_);
                                            leanh::lean_dec(v___x_2146_);
                                            v___x_2224_ = leanh::lean_box(0);
                                            v_isShared_2225_ = v_isSharedCheck_2229_;
                                            state = 20;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2143_);
                                    leanh::lean_dec(v_injDeclName_2138_);
                                    leanh::lean_dec_ref(v_b_2042_);
                                    leanh::lean_dec_ref(v_a_2041_);
                                    v_a_2230_ = leanh::lean_ctor_get(v___x_2144_, 0);
                                    v_isSharedCheck_2237_ =
                                        (!leanh::lean_is_exclusive(v___x_2144_)) as u8;
                                    if v_isSharedCheck_2237_ == 0 {
                                        v___x_2232_ = v___x_2144_;
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 22;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2230_);
                                        leanh::lean_dec(v___x_2144_);
                                        v___x_2232_ = leanh::lean_box(0);
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_injDeclName_2138_);
                                leanh::lean_dec_ref(v_b_2042_);
                                leanh::lean_dec_ref(v_a_2041_);
                                v_a_2238_ = leanh::lean_ctor_get(v___x_2142_, 0);
                                v_isSharedCheck_2245_ =
                                    (!leanh::lean_is_exclusive(v___x_2142_)) as u8;
                                if v_isSharedCheck_2245_ == 0 {
                                    v___x_2240_ = v___x_2142_;
                                    v_isShared_2241_ = v_isSharedCheck_2245_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2238_);
                                    leanh::lean_dec(v___x_2142_);
                                    v___x_2240_ = leanh::lean_box(0);
                                    v_isShared_2241_ = v_isSharedCheck_2245_;
                                    state = 24;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_ctor_u2081_2089_);
                        leanh::lean_dec_ref(v_b_2042_);
                        leanh::lean_dec_ref(v_a_2041_);
                        v___x_2246_ = leanh::lean_box(0);
                        v___x_2247_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2247_, 0, v___x_2246_);
                        return v___x_2247_;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_2052_);
                leanh::lean_inc_ref(v_a_2051_);
                leanh::lean_inc(v_a_2050_);
                leanh::lean_inc_ref(v_a_2049_);
                leanh::lean_inc_ref(v_a_2055_);
                v___x_2056_ =
                    lean_infer_type(v_a_2055_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                if leanh::lean_obj_tag(v___x_2056_) == 0 {
                    v_a_2057_ = leanh::lean_ctor_get(v___x_2056_, 0);
                    leanh::lean_inc(v_a_2057_);
                    leanh::lean_dec_ref_known(v___x_2056_, 1);
                    v___x_2058_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2041_, v_a_2043_);
                    leanh::lean_dec_ref(v_a_2041_);
                    if leanh::lean_obj_tag(v___x_2058_) == 0 {
                        v_a_2059_ = leanh::lean_ctor_get(v___x_2058_, 0);
                        leanh::lean_inc(v_a_2059_);
                        leanh::lean_dec_ref_known(v___x_2058_, 1);
                        v___x_2060_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_b_2042_, v_a_2043_);
                        leanh::lean_dec_ref(v_b_2042_);
                        if leanh::lean_obj_tag(v___x_2060_) == 0 {
                            v_a_2061_ = leanh::lean_ctor_get(v___x_2060_, 0);
                            leanh::lean_inc(v_a_2061_);
                            leanh::lean_dec_ref_known(v___x_2060_, 1);
                            v___x_2062_ = lean_nat_dec_le(v_a_2059_, v_a_2061_);
                            if v___x_2062_ == 0 {
                                leanh::lean_dec(v_a_2061_);
                                v___x_2063_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(v_a_2057_, v_a_2055_, v_a_2059_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                                return v___x_2063_;
                            } else {
                                leanh::lean_dec(v_a_2059_);
                                v___x_2064_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(v_a_2057_, v_a_2055_, v_a_2061_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                                return v___x_2064_;
                            }
                        } else {
                            leanh::lean_dec(v_a_2059_);
                            leanh::lean_dec(v_a_2057_);
                            leanh::lean_dec_ref(v_a_2055_);
                            v_a_2065_ = leanh::lean_ctor_get(v___x_2060_, 0);
                            v_isSharedCheck_2072_ =
                                (!leanh::lean_is_exclusive(v___x_2060_)) as u8;
                            if v_isSharedCheck_2072_ == 0 {
                                v___x_2067_ = v___x_2060_;
                                v_isShared_2068_ = v_isSharedCheck_2072_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2065_);
                                leanh::lean_dec(v___x_2060_);
                                v___x_2067_ = leanh::lean_box(0);
                                v_isShared_2068_ = v_isSharedCheck_2072_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2057_);
                        leanh::lean_dec_ref(v_a_2055_);
                        leanh::lean_dec_ref(v_b_2042_);
                        v_a_2073_ = leanh::lean_ctor_get(v___x_2058_, 0);
                        v_isSharedCheck_2080_ =
                            (!leanh::lean_is_exclusive(v___x_2058_)) as u8;
                        if v_isSharedCheck_2080_ == 0 {
                            v___x_2075_ = v___x_2058_;
                            v_isShared_2076_ = v_isSharedCheck_2080_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2073_);
                            leanh::lean_dec(v___x_2058_);
                            v___x_2075_ = leanh::lean_box(0);
                            v_isShared_2076_ = v_isSharedCheck_2080_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_2055_);
                    leanh::lean_dec_ref(v_b_2042_);
                    leanh::lean_dec_ref(v_a_2041_);
                    v_a_2081_ = leanh::lean_ctor_get(v___x_2056_, 0);
                    v_isSharedCheck_2088_ = (!leanh::lean_is_exclusive(v___x_2056_)) as u8;
                    if v_isSharedCheck_2088_ == 0 {
                        v___x_2083_ = v___x_2056_;
                        v_isShared_2084_ = v_isSharedCheck_2088_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2081_);
                        leanh::lean_dec(v___x_2056_);
                        v___x_2083_ = leanh::lean_box(0);
                        v_isShared_2084_ = v_isSharedCheck_2088_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2068_ == 0 {
                    v___x_2070_ = v___x_2067_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
                    v___x_2070_ = v_reuseFailAlloc_2071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2070_;
            }
            4 => {
                if v_isShared_2076_ == 0 {
                    v___x_2078_ = v___x_2075_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
                    v___x_2078_ = v_reuseFailAlloc_2079_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2078_;
            }
            6 => {
                if v_isShared_2084_ == 0 {
                    v___x_2086_ = v___x_2083_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2086_;
            }
            8 => {
                if v_isShared_2112_ == 0 {
                    v___x_2114_ = v___x_2111_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
                    v___x_2114_ = v_reuseFailAlloc_2115_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2114_;
            }
            10 => {
                if v_isShared_2120_ == 0 {
                    v___x_2122_ = v___x_2119_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
                    v___x_2122_ = v_reuseFailAlloc_2123_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2122_;
            }
            12 => {
                if v_isShared_2128_ == 0 {
                    v___x_2130_ = v___x_2127_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
                    v___x_2130_ = v_reuseFailAlloc_2131_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2130_;
            }
            14 => {
                v_trackZetaDelta_2172_ = leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2173_ = leanh::lean_ctor_get(v_a_2049_, 1);
                v_lctx_2174_ = leanh::lean_ctor_get(v_a_2049_, 2);
                v_localInstances_2175_ = leanh::lean_ctor_get(v_a_2049_, 3);
                v_defEqCtx_x3f_2176_ = leanh::lean_ctor_get(v_a_2049_, 4);
                v_synthPendingDepth_2177_ = leanh::lean_ctor_get(v_a_2049_, 5);
                v_canUnfold_x3f_2178_ = leanh::lean_ctor_get(v_a_2049_, 6);
                v_univApprox_2179_ = leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2180_ = leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2181_ = leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2182_ = 1;
                if v_isShared_2171_ == 0 {
                    v_config_2184_ = v___x_2170_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2212_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        0 as u32,
                        v_foApprox_2151_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        1 as u32,
                        v_ctxApprox_2152_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        2 as u32,
                        v_quasiPatternApprox_2153_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        3 as u32,
                        v_constApprox_2154_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        4 as u32,
                        v_isDefEqStuckEx_2155_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        5 as u32,
                        v_unificationHints_2156_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        6 as u32,
                        v_proofIrrelevance_2157_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        7 as u32,
                        v_assignSyntheticOpaque_2158_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        8 as u32,
                        v_offsetCnstrs_2159_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        10 as u32,
                        v_etaStruct_2160_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        11 as u32,
                        v_univApprox_2161_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        12 as u32,
                        v_iota_2162_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        13 as u32,
                        v_beta_2163_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        14 as u32,
                        v_proj_2164_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        15 as u32,
                        v_zeta_2165_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        16 as u32,
                        v_zetaDelta_2166_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        17 as u32,
                        v_zetaUnused_2167_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        18 as u32,
                        v_zetaHave_2168_,
                    );
                    v_config_2184_ = v_reuseFailAlloc_2212_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_ctor_set_uint8(v_config_2184_, 9 as u32, v___x_2182_);
                v___x_2185_ = l_Lean_Meta_Context_configKey(v_a_2049_);
                v___x_2186_ = 3u64;
                v___x_2187_ = lean_uint64_shift_right(v___x_2185_, v___x_2186_);
                v___x_2188_ = l_Lean_ConstantInfo_type(v_a_2143_);
                leanh::lean_dec(v_a_2143_);
                v___x_2189_ = l_Lean_Expr_getForallArity(v___x_2188_);
                v___x_2190_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_2189_);
                v___x_2191_ = lean_mk_array(v___x_2189_, v___x_2190_);
                v___x_2192_ = leanh::lean_unsigned_to_nat(1);
                v___x_2193_ = lean_nat_sub(v___x_2189_, v___x_2192_);
                leanh::lean_dec(v___x_2189_);
                v___x_2194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2194_, 0, v_a_2149_);
                v___x_2195_ = lean_array_set(v___x_2191_, v___x_2193_, v___x_2194_);
                leanh::lean_dec(v___x_2193_);
                v___x_2196_ = lean_uint64_shift_left(v___x_2187_, v___x_2186_);
                v___x_2197_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1);
                v_key_2198_ = lean_uint64_lor(v___x_2196_, v___x_2197_);
                v___x_2199_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2199_, 0, v_config_2184_);
                leanh::lean_ctor_set_uint64(
                    v___x_2199_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2198_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2178_);
                leanh::lean_inc(v_synthPendingDepth_2177_);
                leanh::lean_inc(v_defEqCtx_x3f_2176_);
                leanh::lean_inc_ref(v_localInstances_2175_);
                leanh::lean_inc_ref(v_lctx_2174_);
                leanh::lean_inc(v_zetaDeltaSet_2173_);
                v___x_2200_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                leanh::lean_ctor_set(v___x_2200_, 1, v_zetaDeltaSet_2173_);
                leanh::lean_ctor_set(v___x_2200_, 2, v_lctx_2174_);
                leanh::lean_ctor_set(v___x_2200_, 3, v_localInstances_2175_);
                leanh::lean_ctor_set(v___x_2200_, 4, v_defEqCtx_x3f_2176_);
                leanh::lean_ctor_set(v___x_2200_, 5, v_synthPendingDepth_2177_);
                leanh::lean_ctor_set(v___x_2200_, 6, v_canUnfold_x3f_2178_);
                leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2172_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2179_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2180_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2181_,
                );
                v___x_2201_ = l_Lean_Meta_mkAppOptM(
                    v_injDeclName_2138_,
                    v___x_2195_,
                    v___x_2200_,
                    v_a_2050_,
                    v_a_2051_,
                    v_a_2052_,
                );
                leanh::lean_dec_ref_known(v___x_2200_, 7);
                if leanh::lean_obj_tag(v___x_2201_) == 0 {
                    v_a_2202_ = leanh::lean_ctor_get(v___x_2201_, 0);
                    leanh::lean_inc(v_a_2202_);
                    leanh::lean_dec_ref_known(v___x_2201_, 1);
                    v_a_2055_ = v_a_2202_;
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_2201_) == 0 {
                        v_a_2203_ = leanh::lean_ctor_get(v___x_2201_, 0);
                        leanh::lean_inc(v_a_2203_);
                        leanh::lean_dec_ref_known(v___x_2201_, 1);
                        v_a_2055_ = v_a_2203_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_2042_);
                        leanh::lean_dec_ref(v_a_2041_);
                        v_a_2204_ = leanh::lean_ctor_get(v___x_2201_, 0);
                        v_isSharedCheck_2211_ =
                            (!leanh::lean_is_exclusive(v___x_2201_)) as u8;
                        if v_isSharedCheck_2211_ == 0 {
                            v___x_2206_ = v___x_2201_;
                            v_isShared_2207_ = v_isSharedCheck_2211_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2204_);
                            leanh::lean_dec(v___x_2201_);
                            v___x_2206_ = leanh::lean_box(0);
                            v_isShared_2207_ = v_isSharedCheck_2211_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            16 => {
                if v_isShared_2207_ == 0 {
                    v___x_2209_ = v___x_2206_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
                    v___x_2209_ = v_reuseFailAlloc_2210_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2209_;
            }
            18 => {
                if v_isShared_2217_ == 0 {
                    v___x_2219_ = v___x_2216_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2220_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
                    v___x_2219_ = v_reuseFailAlloc_2220_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2219_;
            }
            20 => {
                if v_isShared_2225_ == 0 {
                    v___x_2227_ = v___x_2224_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
                    v___x_2227_ = v_reuseFailAlloc_2228_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2227_;
            }
            22 => {
                if v_isShared_2233_ == 0 {
                    v___x_2235_ = v___x_2232_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2235_;
            }
            24 => {
                if v_isShared_2241_ == 0 {
                    v___x_2243_ = v___x_2240_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
                    v___x_2243_ = v_reuseFailAlloc_2244_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___boxed(
    mut v_00_u03b1_2248_: *mut leanh::LeanObject,
    mut v_a_2249_: *mut leanh::LeanObject,
    mut v_b_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
    mut v_a_2255_: *mut leanh::LeanObject,
    mut v_a_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo(
        v_00_u03b1_2248_,
        v_a_2249_,
        v_b_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
        v_a_2255_,
        v_a_2256_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
        v_a_2260_,
    );
    leanh::lean_dec(v_a_2260_);
    leanh::lean_dec_ref(v_a_2259_);
    leanh::lean_dec(v_a_2258_);
    leanh::lean_dec_ref(v_a_2257_);
    leanh::lean_dec(v_a_2256_);
    leanh::lean_dec_ref(v_a_2255_);
    leanh::lean_dec(v_a_2254_);
    leanh::lean_dec_ref(v_a_2253_);
    leanh::lean_dec(v_a_2252_);
    leanh::lean_dec(v_a_2251_);
    leanh::lean_dec_ref(v_00_u03b1_2248_);
    return v_res_2262_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0(
    mut v_00_u03b1_2263_: *mut leanh::LeanObject,
    mut v_constName_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
    mut v___y_2269_: *mut leanh::LeanObject,
    mut v___y_2270_: *mut leanh::LeanObject,
    mut v___y_2271_: *mut leanh::LeanObject,
    mut v___y_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(v_constName_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
    return v___x_2276_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___boxed(
    mut v_00_u03b1_2277_: *mut leanh::LeanObject,
    mut v_constName_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
    mut v___y_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0(v_00_u03b1_2277_, v_constName_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
    leanh::lean_dec(v___y_2288_);
    leanh::lean_dec_ref(v___y_2287_);
    leanh::lean_dec(v___y_2286_);
    leanh::lean_dec_ref(v___y_2285_);
    leanh::lean_dec(v___y_2284_);
    leanh::lean_dec_ref(v___y_2283_);
    leanh::lean_dec(v___y_2282_);
    leanh::lean_dec_ref(v___y_2281_);
    leanh::lean_dec(v___y_2280_);
    leanh::lean_dec(v___y_2279_);
    return v_res_2290_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2291_: *mut leanh::LeanObject,
    mut v_ref_2292_: *mut leanh::LeanObject,
    mut v_constName_2293_: *mut leanh::LeanObject,
    mut v___y_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(v_ref_2292_, v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
    return v___x_2305_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2306_: *mut leanh::LeanObject,
    mut v_ref_2307_: *mut leanh::LeanObject,
    mut v_constName_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
    mut v___y_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1(v_00_u03b1_2306_, v_ref_2307_, v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
    leanh::lean_dec(v___y_2318_);
    leanh::lean_dec_ref(v___y_2317_);
    leanh::lean_dec(v___y_2316_);
    leanh::lean_dec_ref(v___y_2315_);
    leanh::lean_dec(v___y_2314_);
    leanh::lean_dec_ref(v___y_2313_);
    leanh::lean_dec(v___y_2312_);
    leanh::lean_dec_ref(v___y_2311_);
    leanh::lean_dec(v___y_2310_);
    leanh::lean_dec(v___y_2309_);
    leanh::lean_dec(v_ref_2307_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_2321_: *mut leanh::LeanObject,
    mut v_ref_2322_: *mut leanh::LeanObject,
    mut v_msg_2323_: *mut leanh::LeanObject,
    mut v_declHint_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
    mut v___y_2327_: *mut leanh::LeanObject,
    mut v___y_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2322_, v_msg_2323_, v_declHint_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_2337_: *mut leanh::LeanObject,
    mut v_ref_2338_: *mut leanh::LeanObject,
    mut v_msg_2339_: *mut leanh::LeanObject,
    mut v_declHint_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2337_, v_ref_2338_, v_msg_2339_, v_declHint_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
    leanh::lean_dec(v___y_2350_);
    leanh::lean_dec_ref(v___y_2349_);
    leanh::lean_dec(v___y_2348_);
    leanh::lean_dec_ref(v___y_2347_);
    leanh::lean_dec(v___y_2346_);
    leanh::lean_dec_ref(v___y_2345_);
    leanh::lean_dec(v___y_2344_);
    leanh::lean_dec_ref(v___y_2343_);
    leanh::lean_dec(v___y_2342_);
    leanh::lean_dec(v___y_2341_);
    leanh::lean_dec(v_ref_2338_);
    return v_res_2352_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_2353_: *mut leanh::LeanObject,
    mut v_declHint_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
    mut v___y_2359_: *mut leanh::LeanObject,
    mut v___y_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
    mut v___y_2363_: *mut leanh::LeanObject,
    mut v___y_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2353_, v_declHint_2354_, v___y_2364_);
    return v___x_2366_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_2367_: *mut leanh::LeanObject,
    mut v_declHint_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
    mut v___y_2374_: *mut leanh::LeanObject,
    mut v___y_2375_: *mut leanh::LeanObject,
    mut v___y_2376_: *mut leanh::LeanObject,
    mut v___y_2377_: *mut leanh::LeanObject,
    mut v___y_2378_: *mut leanh::LeanObject,
    mut v___y_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2367_, v_declHint_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
    leanh::lean_dec(v___y_2378_);
    leanh::lean_dec_ref(v___y_2377_);
    leanh::lean_dec(v___y_2376_);
    leanh::lean_dec_ref(v___y_2375_);
    leanh::lean_dec(v___y_2374_);
    leanh::lean_dec_ref(v___y_2373_);
    leanh::lean_dec(v___y_2372_);
    leanh::lean_dec_ref(v___y_2371_);
    leanh::lean_dec(v___y_2370_);
    leanh::lean_dec(v___y_2369_);
    return v_res_2380_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_2381_: *mut leanh::LeanObject,
    mut v_ref_2382_: *mut leanh::LeanObject,
    mut v_msg_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
    mut v___y_2386_: *mut leanh::LeanObject,
    mut v___y_2387_: *mut leanh::LeanObject,
    mut v___y_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2382_, v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    return v___x_2395_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_2396_: *mut leanh::LeanObject,
    mut v_ref_2397_: *mut leanh::LeanObject,
    mut v_msg_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: *mut leanh::LeanObject,
    mut v___y_2406_: *mut leanh::LeanObject,
    mut v___y_2407_: *mut leanh::LeanObject,
    mut v___y_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2410_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2396_, v_ref_2397_, v_msg_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
    leanh::lean_dec(v___y_2408_);
    leanh::lean_dec_ref(v___y_2407_);
    leanh::lean_dec(v___y_2406_);
    leanh::lean_dec_ref(v___y_2405_);
    leanh::lean_dec(v___y_2404_);
    leanh::lean_dec_ref(v___y_2403_);
    leanh::lean_dec(v___y_2402_);
    leanh::lean_dec_ref(v___y_2401_);
    leanh::lean_dec(v___y_2400_);
    leanh::lean_dec(v___y_2399_);
    leanh::lean_dec(v_ref_2397_);
    return v_res_2410_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_2411_: *mut leanh::LeanObject,
    mut v_msg_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
    mut v___y_2414_: *mut leanh::LeanObject,
    mut v___y_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
    mut v___y_2419_: *mut leanh::LeanObject,
    mut v___y_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2412_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
    return v___x_2424_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2425_: *mut leanh::LeanObject,
    mut v_msg_2426_: *mut leanh::LeanObject,
    mut v___y_2427_: *mut leanh::LeanObject,
    mut v___y_2428_: *mut leanh::LeanObject,
    mut v___y_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
    mut v___y_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
    mut v___y_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
    mut v___y_2436_: *mut leanh::LeanObject,
    mut v___y_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2425_, v_msg_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
    leanh::lean_dec(v___y_2436_);
    leanh::lean_dec_ref(v___y_2435_);
    leanh::lean_dec(v___y_2434_);
    leanh::lean_dec_ref(v___y_2433_);
    leanh::lean_dec(v___y_2432_);
    leanh::lean_dec_ref(v___y_2431_);
    leanh::lean_dec(v___y_2430_);
    leanh::lean_dec_ref(v___y_2429_);
    leanh::lean_dec(v___y_2428_);
    leanh::lean_dec(v___y_2427_);
    return v_res_2438_;
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(
    mut v_x_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
    mut v___y_2442_: *mut leanh::LeanObject,
    mut v___y_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2439_) == 0 {
                    v___x_2445_ = 1;
                    v___x_2446_ = leanh::lean_box((v___x_2445_) as usize);
                    v___x_2447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2447_, 0, v___x_2446_);
                    return v___x_2447_;
                } else {
                    v_head_2448_ = leanh::lean_ctor_get(v_x_2439_, 0);
                    leanh::lean_inc(v_head_2448_);
                    v_tail_2449_ = leanh::lean_ctor_get(v_x_2439_, 1);
                    leanh::lean_inc(v_tail_2449_);
                    leanh::lean_dec_ref_known(v_x_2439_, 2);
                    v_fst_2450_ = leanh::lean_ctor_get(v_head_2448_, 0);
                    leanh::lean_inc(v_fst_2450_);
                    v_snd_2451_ = leanh::lean_ctor_get(v_head_2448_, 1);
                    leanh::lean_inc(v_snd_2451_);
                    leanh::lean_dec(v_head_2448_);
                    v___x_2452_ = l_Lean_Meta_isLevelDefEq(
                        v_fst_2450_,
                        v_snd_2451_,
                        v___y_2440_,
                        v___y_2441_,
                        v___y_2442_,
                        v___y_2443_,
                    );
                    if leanh::lean_obj_tag(v___x_2452_) == 0 {
                        v_a_2453_ = leanh::lean_ctor_get(v___x_2452_, 0);
                        leanh::lean_inc(v_a_2453_);
                        v___x_2454_ = (leanh::lean_unbox(v_a_2453_) as u8);
                        leanh::lean_dec(v_a_2453_);
                        if v___x_2454_ == 0 {
                            leanh::lean_dec(v_tail_2449_);
                            return v___x_2452_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2452_, 1);
                            v_x_2439_ = v_tail_2449_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_2449_);
                        return v___x_2452_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg___boxed(
    mut v_x_2456_: *mut leanh::LeanObject,
    mut v___y_2457_: *mut leanh::LeanObject,
    mut v___y_2458_: *mut leanh::LeanObject,
    mut v___y_2459_: *mut leanh::LeanObject,
    mut v___y_2460_: *mut leanh::LeanObject,
    mut v___y_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(v_x_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
    leanh::lean_dec(v___y_2460_);
    leanh::lean_dec_ref(v___y_2459_);
    leanh::lean_dec(v___y_2458_);
    leanh::lean_dec_ref(v___y_2457_);
    return v_res_2462_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = leanh::lean_unsigned_to_nat(0);
    v___x_2464_ = l_Lean_Level_ofNat(v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(
    mut v_ctor_u2081_2465_: *mut leanh::LeanObject,
    mut v_args_u2081_2466_: *mut leanh::LeanObject,
    mut v_a_2467_: *mut leanh::LeanObject,
    mut v_b_2468_: *mut leanh::LeanObject,
    mut v_x_2469_: *mut leanh::LeanObject,
    mut v_x_2470_: *mut leanh::LeanObject,
    mut v_x_2471_: *mut leanh::LeanObject,
    mut v___y_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
    mut v___y_2478_: *mut leanh::LeanObject,
    mut v___y_2479_: *mut leanh::LeanObject,
    mut v___y_2480_: *mut leanh::LeanObject,
    mut v___y_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v_declName_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v_val_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v_val_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v_val_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v_val_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut v_a_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_a_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut v_a_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2659_: u8 = 0;
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut v_a_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut v_a_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2680_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_a_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_start_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_a_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2469_) == 5 {
                    v_fn_2483_ = leanh::lean_ctor_get(v_x_2469_, 0);
                    leanh::lean_inc_ref(v_fn_2483_);
                    v_arg_2484_ = leanh::lean_ctor_get(v_x_2469_, 1);
                    leanh::lean_inc_ref(v_arg_2484_);
                    leanh::lean_dec_ref_known(v_x_2469_, 2);
                    v___x_2485_ = lean_array_set(v_x_2470_, v_x_2471_, v_arg_2484_);
                    v___x_2486_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2487_ = lean_nat_sub(v_x_2471_, v___x_2486_);
                    leanh::lean_dec(v_x_2471_);
                    v_x_2469_ = v_fn_2483_;
                    v_x_2470_ = v___x_2485_;
                    v_x_2471_ = v___x_2487_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_2471_);
                    if leanh::lean_obj_tag(v_ctor_u2081_2465_) == 4 {
                        v_declName_2489_ = leanh::lean_ctor_get(v_ctor_u2081_2465_, 0);
                        leanh::lean_inc(v_declName_2489_);
                        v_us_2490_ = leanh::lean_ctor_get(v_ctor_u2081_2465_, 1);
                        leanh::lean_inc(v_us_2490_);
                        leanh::lean_dec_ref_known(v_ctor_u2081_2465_, 2);
                        if leanh::lean_obj_tag(v_x_2469_) == 4 {
                            v_declName_2521_ = leanh::lean_ctor_get(v_x_2469_, 0);
                            leanh::lean_inc(v_declName_2521_);
                            v_us_2522_ = leanh::lean_ctor_get(v_x_2469_, 1);
                            leanh::lean_inc(v_us_2522_);
                            leanh::lean_dec_ref_known(v_x_2469_, 2);
                            leanh::lean_inc(v_declName_2489_);
                            v___x_2523_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_declName_2489_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
                            if leanh::lean_obj_tag(v___x_2523_) == 0 {
                                v_a_2524_ = leanh::lean_ctor_get(v___x_2523_, 0);
                                v_isSharedCheck_2720_ =
                                    (!leanh::lean_is_exclusive(v___x_2523_)) as u8;
                                if v_isSharedCheck_2720_ == 0 {
                                    v___x_2526_ = v___x_2523_;
                                    v_isShared_2527_ = v_isSharedCheck_2720_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2524_);
                                    leanh::lean_dec(v___x_2523_);
                                    v___x_2526_ = leanh::lean_box(0);
                                    v_isShared_2527_ = v_isSharedCheck_2720_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_us_2522_);
                                leanh::lean_dec(v_declName_2521_);
                                leanh::lean_dec(v_us_2490_);
                                leanh::lean_dec(v_declName_2489_);
                                leanh::lean_dec_ref(v_x_2470_);
                                leanh::lean_dec_ref(v_b_2468_);
                                leanh::lean_dec_ref(v_a_2467_);
                                leanh::lean_dec_ref(v_args_u2081_2466_);
                                v_a_2721_ = leanh::lean_ctor_get(v___x_2523_, 0);
                                v_isSharedCheck_2728_ =
                                    (!leanh::lean_is_exclusive(v___x_2523_)) as u8;
                                if v_isSharedCheck_2728_ == 0 {
                                    v___x_2723_ = v___x_2523_;
                                    v_isShared_2724_ = v_isSharedCheck_2728_;
                                    state = 39;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2721_);
                                    leanh::lean_dec(v___x_2523_);
                                    v___x_2723_ = leanh::lean_box(0);
                                    v_isShared_2724_ = v_isSharedCheck_2728_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_us_2490_);
                            leanh::lean_dec(v_declName_2489_);
                            leanh::lean_dec_ref(v_x_2470_);
                            leanh::lean_dec_ref(v_x_2469_);
                            leanh::lean_dec_ref(v_b_2468_);
                            leanh::lean_dec_ref(v_a_2467_);
                            leanh::lean_dec_ref(v_args_u2081_2466_);
                            v___x_2729_ = leanh::lean_box(0);
                            v___x_2730_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2730_, 0, v___x_2729_);
                            return v___x_2730_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_2470_);
                        leanh::lean_dec_ref(v_x_2469_);
                        leanh::lean_dec_ref(v_b_2468_);
                        leanh::lean_dec_ref(v_a_2467_);
                        leanh::lean_dec_ref(v_args_u2081_2466_);
                        leanh::lean_dec_ref(v_ctor_u2081_2465_);
                        v___x_2731_ = leanh::lean_box(0);
                        v___x_2732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2732_, 0, v___x_2731_);
                        return v___x_2732_;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_2493_);
                v___x_2504_ = l_Lean_mkConst(v___y_2493_, v_us_2490_);
                v___x_2505_ = l_Lean_mkAppN(v___x_2504_, v_args_u2081_2466_);
                leanh::lean_dec_ref(v_args_u2081_2466_);
                v___x_2506_ = l_Lean_mkAppN(v___x_2505_, v_x_2470_);
                leanh::lean_dec_ref(v_x_2470_);
                leanh::lean_inc(v___y_2503_);
                leanh::lean_inc_ref(v___y_2502_);
                leanh::lean_inc(v___y_2501_);
                leanh::lean_inc_ref(v___y_2500_);
                leanh::lean_inc_ref(v___x_2506_);
                v___x_2507_ = lean_infer_type(
                    v___x_2506_,
                    v___y_2500_,
                    v___y_2501_,
                    v___y_2502_,
                    v___y_2503_,
                );
                if leanh::lean_obj_tag(v___x_2507_) == 0 {
                    v_a_2508_ = leanh::lean_ctor_get(v___x_2507_, 0);
                    leanh::lean_inc(v_a_2508_);
                    leanh::lean_dec_ref_known(v___x_2507_, 1);
                    v___x_2509_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2509_, 0, v___y_2493_);
                    v___x_2510_ = leanh::lean_alloc_ctor(7, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2510_, 0, v___x_2509_);
                    v___x_2511_ = leanh::lean_box(1);
                    v___x_2512_ = l_Lean_Meta_Grind_addNewRawFact(
                        v___x_2506_,
                        v_a_2508_,
                        v___y_2492_,
                        v___x_2510_,
                        v___x_2511_,
                        v___y_2494_,
                        v___y_2495_,
                        v___y_2496_,
                        v___y_2497_,
                        v___y_2498_,
                        v___y_2499_,
                        v___y_2500_,
                        v___y_2501_,
                        v___y_2502_,
                        v___y_2503_,
                    );
                    return v___x_2512_;
                } else {
                    leanh::lean_dec_ref(v___x_2506_);
                    leanh::lean_dec(v___y_2493_);
                    leanh::lean_dec(v___y_2492_);
                    v_a_2513_ = leanh::lean_ctor_get(v___x_2507_, 0);
                    v_isSharedCheck_2520_ = (!leanh::lean_is_exclusive(v___x_2507_)) as u8;
                    if v_isSharedCheck_2520_ == 0 {
                        v___x_2515_ = v___x_2507_;
                        v_isShared_2516_ = v_isSharedCheck_2520_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2513_);
                        leanh::lean_dec(v___x_2507_);
                        v___x_2515_ = leanh::lean_box(0);
                        v_isShared_2516_ = v_isSharedCheck_2520_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2516_ == 0 {
                    v___x_2518_ = v___x_2515_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2519_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
                    v___x_2518_ = v_reuseFailAlloc_2519_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2518_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_2524_) == 6 {
                    v_val_2528_ = leanh::lean_ctor_get(v_a_2524_, 0);
                    leanh::lean_inc_ref(v_val_2528_);
                    leanh::lean_dec_ref_known(v_a_2524_, 1);
                    leanh::lean_inc(v_declName_2521_);
                    v___x_2529_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_declName_2521_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
                    if leanh::lean_obj_tag(v___x_2529_) == 0 {
                        v_a_2530_ = leanh::lean_ctor_get(v___x_2529_, 0);
                        v_isSharedCheck_2707_ =
                            (!leanh::lean_is_exclusive(v___x_2529_)) as u8;
                        if v_isSharedCheck_2707_ == 0 {
                            v___x_2532_ = v___x_2529_;
                            v_isShared_2533_ = v_isSharedCheck_2707_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2530_);
                            leanh::lean_dec(v___x_2529_);
                            v___x_2532_ = leanh::lean_box(0);
                            v_isShared_2533_ = v_isSharedCheck_2707_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_val_2528_);
                        leanh::lean_del_object(v___x_2526_);
                        leanh::lean_dec(v_us_2522_);
                        leanh::lean_dec(v_declName_2521_);
                        leanh::lean_dec(v_us_2490_);
                        leanh::lean_dec(v_declName_2489_);
                        leanh::lean_dec_ref(v_x_2470_);
                        leanh::lean_dec_ref(v_b_2468_);
                        leanh::lean_dec_ref(v_a_2467_);
                        leanh::lean_dec_ref(v_args_u2081_2466_);
                        v_a_2708_ = leanh::lean_ctor_get(v___x_2529_, 0);
                        v_isSharedCheck_2715_ =
                            (!leanh::lean_is_exclusive(v___x_2529_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2710_ = v___x_2529_;
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 36;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2708_);
                            leanh::lean_dec(v___x_2529_);
                            v___x_2710_ = leanh::lean_box(0);
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 36;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2524_);
                    leanh::lean_dec(v_us_2522_);
                    leanh::lean_dec(v_declName_2521_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec(v_declName_2489_);
                    leanh::lean_dec_ref(v_x_2470_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2716_ = leanh::lean_box(0);
                    if v_isShared_2527_ == 0 {
                        leanh::lean_ctor_set(v___x_2526_, 0, v___x_2716_);
                        v___x_2718_ = v___x_2526_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2719_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                        v___x_2718_ = v_reuseFailAlloc_2719_;
                        state = 38;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_2530_) == 6 {
                    v_val_2534_ = leanh::lean_ctor_get(v_a_2530_, 0);
                    leanh::lean_inc_ref(v_val_2534_);
                    leanh::lean_dec_ref_known(v_a_2530_, 1);
                    v_induct_2535_ = leanh::lean_ctor_get(v_val_2528_, 1);
                    leanh::lean_inc(v_induct_2535_);
                    v_numParams_2536_ = leanh::lean_ctor_get(v_val_2528_, 3);
                    leanh::lean_inc(v_numParams_2536_);
                    leanh::lean_dec_ref(v_val_2528_);
                    v_induct_2537_ = leanh::lean_ctor_get(v_val_2534_, 1);
                    leanh::lean_inc(v_induct_2537_);
                    v_numParams_2538_ = leanh::lean_ctor_get(v_val_2534_, 3);
                    leanh::lean_inc(v_numParams_2538_);
                    leanh::lean_dec_ref(v_val_2534_);
                    v___x_2539_ = lean_name_eq(v_induct_2535_, v_induct_2537_);
                    leanh::lean_dec(v_induct_2537_);
                    if v___x_2539_ == 0 {
                        leanh::lean_dec(v_numParams_2538_);
                        leanh::lean_dec(v_numParams_2536_);
                        leanh::lean_dec(v_induct_2535_);
                        leanh::lean_del_object(v___x_2526_);
                        leanh::lean_dec(v_us_2522_);
                        leanh::lean_dec(v_declName_2521_);
                        leanh::lean_dec(v_us_2490_);
                        leanh::lean_dec(v_declName_2489_);
                        leanh::lean_dec_ref(v_x_2470_);
                        leanh::lean_dec_ref(v_b_2468_);
                        leanh::lean_dec_ref(v_a_2467_);
                        leanh::lean_dec_ref(v_args_u2081_2466_);
                        v___x_2540_ = leanh::lean_box(0);
                        if v_isShared_2533_ == 0 {
                            leanh::lean_ctor_set(v___x_2532_, 0, v___x_2540_);
                            v___x_2542_ = v___x_2532_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2543_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
                            v___x_2542_ = v_reuseFailAlloc_2543_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_2544_ = leanh::lean_unsigned_to_nat(0);
                        leanh::lean_inc_ref(v_args_u2081_2466_);
                        v___x_2545_ = l_Array_toSubarray___redArg(
                            v_args_u2081_2466_,
                            v___x_2544_,
                            v_numParams_2536_,
                        );
                        v_start_2546_ = leanh::lean_ctor_get(v___x_2545_, 1);
                        leanh::lean_inc(v_start_2546_);
                        v_stop_2547_ = leanh::lean_ctor_get(v___x_2545_, 2);
                        leanh::lean_inc(v_stop_2547_);
                        leanh::lean_inc_ref(v_x_2470_);
                        v___x_2548_ =
                            l_Array_toSubarray___redArg(v_x_2470_, v___x_2544_, v_numParams_2538_);
                        v_start_2694_ = leanh::lean_ctor_get(v___x_2548_, 1);
                        leanh::lean_inc(v_start_2694_);
                        v_stop_2695_ = leanh::lean_ctor_get(v___x_2548_, 2);
                        leanh::lean_inc(v_stop_2695_);
                        v___x_2696_ = lean_nat_sub(v_stop_2547_, v_start_2546_);
                        leanh::lean_dec(v_start_2546_);
                        leanh::lean_dec(v_stop_2547_);
                        v___x_2697_ = lean_nat_sub(v_stop_2695_, v_start_2694_);
                        leanh::lean_dec(v_start_2694_);
                        leanh::lean_dec(v_stop_2695_);
                        v___x_2698_ = lean_nat_dec_eq(v___x_2696_, v___x_2697_);
                        leanh::lean_dec(v___x_2697_);
                        leanh::lean_dec(v___x_2696_);
                        if v___x_2698_ == 0 {
                            if v___x_2539_ == 0 {
                                leanh::lean_del_object(v___x_2526_);
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___x_2548_);
                                leanh::lean_dec_ref(v___x_2545_);
                                leanh::lean_dec(v_induct_2535_);
                                leanh::lean_del_object(v___x_2532_);
                                leanh::lean_dec(v_us_2522_);
                                leanh::lean_dec(v_declName_2521_);
                                leanh::lean_dec(v_us_2490_);
                                leanh::lean_dec(v_declName_2489_);
                                leanh::lean_dec_ref(v_x_2470_);
                                leanh::lean_dec_ref(v_b_2468_);
                                leanh::lean_dec_ref(v_a_2467_);
                                leanh::lean_dec_ref(v_args_u2081_2466_);
                                v___x_2699_ = leanh::lean_box(0);
                                if v_isShared_2527_ == 0 {
                                    leanh::lean_ctor_set(v___x_2526_, 0, v___x_2699_);
                                    v___x_2701_ = v___x_2526_;
                                    state = 34;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2702_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2702_,
                                        0,
                                        v___x_2699_,
                                    );
                                    v___x_2701_ = v_reuseFailAlloc_2702_;
                                    state = 34;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_2526_);
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2530_);
                    leanh::lean_dec_ref(v_val_2528_);
                    leanh::lean_del_object(v___x_2526_);
                    leanh::lean_dec(v_us_2522_);
                    leanh::lean_dec(v_declName_2521_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec(v_declName_2489_);
                    leanh::lean_dec_ref(v_x_2470_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2703_ = leanh::lean_box(0);
                    if v_isShared_2533_ == 0 {
                        leanh::lean_ctor_set(v___x_2532_, 0, v___x_2703_);
                        v___x_2705_ = v___x_2532_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_2706_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
                        v___x_2705_ = v_reuseFailAlloc_2706_;
                        state = 35;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2542_;
            }
            7 => {
                v___x_2551_ = lean_name_eq(v_declName_2489_, v_declName_2521_);
                leanh::lean_dec(v_declName_2521_);
                if v___x_2551_ == 0 {
                    leanh::lean_dec(v_declName_2489_);
                    leanh::lean_dec_ref(v_x_2470_);
                    leanh::lean_dec_ref(v_args_u2081_2466_);
                    leanh::lean_inc_ref(v_a_2467_);
                    v___x_2552_ = l_Lean_Meta_getCtorAppIndices_x3f(
                        v_a_2467_,
                        v___y_2478_,
                        v___y_2479_,
                        v___y_2480_,
                        v___y_2481_,
                    );
                    if leanh::lean_obj_tag(v___x_2552_) == 0 {
                        v_a_2553_ = leanh::lean_ctor_get(v___x_2552_, 0);
                        v_isSharedCheck_2631_ =
                            (!leanh::lean_is_exclusive(v___x_2552_)) as u8;
                        if v_isSharedCheck_2631_ == 0 {
                            v___x_2555_ = v___x_2552_;
                            v_isShared_2556_ = v_isSharedCheck_2631_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2553_);
                            leanh::lean_dec(v___x_2552_);
                            v___x_2555_ = leanh::lean_box(0);
                            v_isShared_2556_ = v_isSharedCheck_2631_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_2550_);
                        leanh::lean_dec_ref(v___x_2548_);
                        leanh::lean_dec_ref(v___x_2545_);
                        leanh::lean_dec(v_induct_2535_);
                        leanh::lean_dec(v_us_2490_);
                        leanh::lean_dec_ref(v_b_2468_);
                        leanh::lean_dec_ref(v_a_2467_);
                        v_a_2632_ = leanh::lean_ctor_get(v___x_2552_, 0);
                        v_isSharedCheck_2639_ =
                            (!leanh::lean_is_exclusive(v___x_2552_)) as u8;
                        if v_isSharedCheck_2639_ == 0 {
                            v___x_2634_ = v___x_2552_;
                            v_isShared_2635_ = v_isSharedCheck_2639_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2632_);
                            leanh::lean_dec(v___x_2552_);
                            v___x_2634_ = leanh::lean_box(0);
                            v_isShared_2635_ = v_isSharedCheck_2639_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    v___x_2640_ = lean_st_ref_get(v___y_2481_);
                    v_env_2641_ = leanh::lean_ctor_get(v___x_2640_, 0);
                    leanh::lean_inc_ref(v_env_2641_);
                    leanh::lean_dec(v___x_2640_);
                    v___x_2642_ = l_Lean_Meta_mkHInjectiveTheoremNameFor(v_declName_2489_);
                    v___x_2643_ = l_Lean_Environment_containsOnBranch(v_env_2641_, v___x_2642_);
                    leanh::lean_dec_ref(v_env_2641_);
                    if v___x_2643_ == 0 {
                        leanh::lean_inc(v___x_2642_);
                        v___x_2644_ =
                            l_Lean_executeReservedNameAction(v___x_2642_, v___y_2480_, v___y_2481_);
                        if leanh::lean_obj_tag(v___x_2644_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2644_, 1);
                            v___y_2492_ = v___y_2550_;
                            v___y_2493_ = v___x_2642_;
                            v___y_2494_ = v___y_2472_;
                            v___y_2495_ = v___y_2473_;
                            v___y_2496_ = v___y_2474_;
                            v___y_2497_ = v___y_2475_;
                            v___y_2498_ = v___y_2476_;
                            v___y_2499_ = v___y_2477_;
                            v___y_2500_ = v___y_2478_;
                            v___y_2501_ = v___y_2479_;
                            v___y_2502_ = v___y_2480_;
                            v___y_2503_ = v___y_2481_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2642_);
                            leanh::lean_dec(v___y_2550_);
                            leanh::lean_dec(v_us_2490_);
                            leanh::lean_dec_ref(v_x_2470_);
                            leanh::lean_dec_ref(v_args_u2081_2466_);
                            return v___x_2644_;
                        }
                    } else {
                        v___y_2492_ = v___y_2550_;
                        v___y_2493_ = v___x_2642_;
                        v___y_2494_ = v___y_2472_;
                        v___y_2495_ = v___y_2473_;
                        v___y_2496_ = v___y_2474_;
                        v___y_2497_ = v___y_2475_;
                        v___y_2498_ = v___y_2476_;
                        v___y_2499_ = v___y_2477_;
                        v___y_2500_ = v___y_2478_;
                        v___y_2501_ = v___y_2479_;
                        v___y_2502_ = v___y_2480_;
                        v___y_2503_ = v___y_2481_;
                        state = 1;
                        continue;
                    }
                }
            }
            8 => {
                if leanh::lean_obj_tag(v_a_2553_) == 1 {
                    leanh::lean_del_object(v___x_2555_);
                    v_val_2557_ = leanh::lean_ctor_get(v_a_2553_, 0);
                    v_isSharedCheck_2626_ = (!leanh::lean_is_exclusive(v_a_2553_)) as u8;
                    if v_isSharedCheck_2626_ == 0 {
                        v___x_2559_ = v_a_2553_;
                        v_isShared_2560_ = v_isSharedCheck_2626_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2557_);
                        leanh::lean_dec(v_a_2553_);
                        v___x_2559_ = leanh::lean_box(0);
                        v_isShared_2560_ = v_isSharedCheck_2626_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2553_);
                    leanh::lean_dec(v___y_2550_);
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    v___x_2627_ = leanh::lean_box(0);
                    if v_isShared_2556_ == 0 {
                        leanh::lean_ctor_set(v___x_2555_, 0, v___x_2627_);
                        v___x_2629_ = v___x_2555_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2630_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
                        v___x_2629_ = v_reuseFailAlloc_2630_;
                        state = 21;
                        continue;
                    }
                }
            }
            9 => {
                leanh::lean_inc_ref(v_b_2468_);
                v___x_2561_ = l_Lean_Meta_getCtorAppIndices_x3f(
                    v_b_2468_,
                    v___y_2478_,
                    v___y_2479_,
                    v___y_2480_,
                    v___y_2481_,
                );
                if leanh::lean_obj_tag(v___x_2561_) == 0 {
                    v_a_2562_ = leanh::lean_ctor_get(v___x_2561_, 0);
                    v_isSharedCheck_2617_ = (!leanh::lean_is_exclusive(v___x_2561_)) as u8;
                    if v_isSharedCheck_2617_ == 0 {
                        v___x_2564_ = v___x_2561_;
                        v_isShared_2565_ = v_isSharedCheck_2617_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2562_);
                        leanh::lean_dec(v___x_2561_);
                        v___x_2564_ = leanh::lean_box(0);
                        v_isShared_2565_ = v_isSharedCheck_2617_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2559_);
                    leanh::lean_dec(v_val_2557_);
                    leanh::lean_dec(v___y_2550_);
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    v_a_2618_ = leanh::lean_ctor_get(v___x_2561_, 0);
                    v_isSharedCheck_2625_ = (!leanh::lean_is_exclusive(v___x_2561_)) as u8;
                    if v_isSharedCheck_2625_ == 0 {
                        v___x_2620_ = v___x_2561_;
                        v_isShared_2621_ = v_isSharedCheck_2625_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2618_);
                        leanh::lean_dec(v___x_2561_);
                        v___x_2620_ = leanh::lean_box(0);
                        v_isShared_2621_ = v_isSharedCheck_2625_;
                        state = 19;
                        continue;
                    }
                }
            }
            10 => {
                if leanh::lean_obj_tag(v_a_2562_) == 1 {
                    leanh::lean_del_object(v___x_2564_);
                    v_val_2566_ = leanh::lean_ctor_get(v_a_2562_, 0);
                    v_isSharedCheck_2612_ = (!leanh::lean_is_exclusive(v_a_2562_)) as u8;
                    if v_isSharedCheck_2612_ == 0 {
                        v___x_2568_ = v_a_2562_;
                        v_isShared_2569_ = v_isSharedCheck_2612_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2566_);
                        leanh::lean_dec(v_a_2562_);
                        v___x_2568_ = leanh::lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2612_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2562_);
                    leanh::lean_del_object(v___x_2559_);
                    leanh::lean_dec(v_val_2557_);
                    leanh::lean_dec(v___y_2550_);
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    v___x_2613_ = leanh::lean_box(0);
                    if v_isShared_2565_ == 0 {
                        leanh::lean_ctor_set(v___x_2564_, 0, v___x_2613_);
                        v___x_2615_ = v___x_2564_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2616_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
                        v___x_2615_ = v_reuseFailAlloc_2616_;
                        state = 18;
                        continue;
                    }
                }
            }
            11 => {
                v___x_2570_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_2476_);
                if leanh::lean_obj_tag(v___x_2570_) == 0 {
                    v_a_2571_ = leanh::lean_ctor_get(v___x_2570_, 0);
                    leanh::lean_inc(v_a_2571_);
                    leanh::lean_dec_ref_known(v___x_2570_, 1);
                    v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0;
                    v___x_2573_ = l_Lean_Name_str___override(v_induct_2535_, v___x_2572_);
                    v___x_2574_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0);
                    v___x_2575_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2575_, 0, v___x_2574_);
                    leanh::lean_ctor_set(v___x_2575_, 1, v_us_2490_);
                    leanh::lean_inc(v___x_2573_);
                    v___x_2576_ = l_Lean_mkConst(v___x_2573_, v___x_2575_);
                    v___x_2577_ = l_Lean_Expr_app___override(v___x_2576_, v_a_2571_);
                    v___x_2578_ = l_Subarray_copy___redArg(v___x_2545_);
                    v___x_2579_ = l_Array_append___redArg(v___x_2578_, v_val_2557_);
                    leanh::lean_dec(v_val_2557_);
                    v___x_2580_ = l_Lean_mkAppN(v___x_2577_, v___x_2579_);
                    leanh::lean_dec_ref(v___x_2579_);
                    v___x_2581_ = l_Lean_Expr_app___override(v___x_2580_, v_a_2467_);
                    v___x_2582_ = l_Subarray_copy___redArg(v___x_2548_);
                    v___x_2583_ = l_Array_append___redArg(v___x_2582_, v_val_2566_);
                    leanh::lean_dec(v_val_2566_);
                    v___x_2584_ = l_Lean_mkAppN(v___x_2581_, v___x_2583_);
                    leanh::lean_dec_ref(v___x_2583_);
                    v___x_2585_ = l_Lean_Expr_app___override(v___x_2584_, v_b_2468_);
                    leanh::lean_inc(v___y_2481_);
                    leanh::lean_inc_ref(v___y_2480_);
                    leanh::lean_inc(v___y_2479_);
                    leanh::lean_inc_ref(v___y_2478_);
                    leanh::lean_inc_ref(v___x_2585_);
                    v___x_2586_ = lean_infer_type(
                        v___x_2585_,
                        v___y_2478_,
                        v___y_2479_,
                        v___y_2480_,
                        v___y_2481_,
                    );
                    if leanh::lean_obj_tag(v___x_2586_) == 0 {
                        v_a_2587_ = leanh::lean_ctor_get(v___x_2586_, 0);
                        leanh::lean_inc(v_a_2587_);
                        leanh::lean_dec_ref_known(v___x_2586_, 1);
                        if v_isShared_2569_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2568_, 0);
                            leanh::lean_ctor_set(v___x_2568_, 0, v___x_2573_);
                            v___x_2589_ = v___x_2568_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2595_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2573_);
                            v___x_2589_ = v_reuseFailAlloc_2595_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2585_);
                        leanh::lean_dec(v___x_2573_);
                        leanh::lean_del_object(v___x_2568_);
                        leanh::lean_del_object(v___x_2559_);
                        leanh::lean_dec(v___y_2550_);
                        v_a_2596_ = leanh::lean_ctor_get(v___x_2586_, 0);
                        v_isSharedCheck_2603_ =
                            (!leanh::lean_is_exclusive(v___x_2586_)) as u8;
                        if v_isSharedCheck_2603_ == 0 {
                            v___x_2598_ = v___x_2586_;
                            v_isShared_2599_ = v_isSharedCheck_2603_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2596_);
                            leanh::lean_dec(v___x_2586_);
                            v___x_2598_ = leanh::lean_box(0);
                            v_isShared_2599_ = v_isSharedCheck_2603_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2568_);
                    leanh::lean_dec(v_val_2566_);
                    leanh::lean_del_object(v___x_2559_);
                    leanh::lean_dec(v_val_2557_);
                    leanh::lean_dec(v___y_2550_);
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    v_a_2604_ = leanh::lean_ctor_get(v___x_2570_, 0);
                    v_isSharedCheck_2611_ = (!leanh::lean_is_exclusive(v___x_2570_)) as u8;
                    if v_isSharedCheck_2611_ == 0 {
                        v___x_2606_ = v___x_2570_;
                        v_isShared_2607_ = v_isSharedCheck_2611_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2604_);
                        leanh::lean_dec(v___x_2570_);
                        v___x_2606_ = leanh::lean_box(0);
                        v_isShared_2607_ = v_isSharedCheck_2611_;
                        state = 16;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2560_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2559_, 7);
                    leanh::lean_ctor_set(v___x_2559_, 0, v___x_2589_);
                    v___x_2591_ = v___x_2559_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2594_ = leanh::lean_alloc_ctor(7, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2589_);
                    v___x_2591_ = v_reuseFailAlloc_2594_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2592_ = leanh::lean_box(1);
                v___x_2593_ = l_Lean_Meta_Grind_addNewRawFact(
                    v___x_2585_,
                    v_a_2587_,
                    v___y_2550_,
                    v___x_2591_,
                    v___x_2592_,
                    v___y_2472_,
                    v___y_2473_,
                    v___y_2474_,
                    v___y_2475_,
                    v___y_2476_,
                    v___y_2477_,
                    v___y_2478_,
                    v___y_2479_,
                    v___y_2480_,
                    v___y_2481_,
                );
                return v___x_2593_;
            }
            14 => {
                if v_isShared_2599_ == 0 {
                    v___x_2601_ = v___x_2598_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
                    v___x_2601_ = v_reuseFailAlloc_2602_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2601_;
            }
            16 => {
                if v_isShared_2607_ == 0 {
                    v___x_2609_ = v___x_2606_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
                    v___x_2609_ = v_reuseFailAlloc_2610_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2609_;
            }
            18 => {
                return v___x_2615_;
            }
            19 => {
                if v_isShared_2621_ == 0 {
                    v___x_2623_ = v___x_2620_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2623_;
            }
            21 => {
                return v___x_2629_;
            }
            22 => {
                if v_isShared_2635_ == 0 {
                    v___x_2637_ = v___x_2634_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2638_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
                    v___x_2637_ = v_reuseFailAlloc_2638_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2637_;
            }
            24 => {
                v___x_2646_ = l_List_lengthTR___redArg(v_us_2490_);
                v___x_2647_ = l_List_lengthTR___redArg(v_us_2522_);
                v___x_2648_ = lean_nat_dec_eq(v___x_2646_, v___x_2647_);
                leanh::lean_dec(v___x_2647_);
                leanh::lean_dec(v___x_2646_);
                if v___x_2648_ == 0 {
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec(v_us_2522_);
                    leanh::lean_dec(v_declName_2521_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec(v_declName_2489_);
                    leanh::lean_dec_ref(v_x_2470_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2649_ = leanh::lean_box(0);
                    if v_isShared_2533_ == 0 {
                        leanh::lean_ctor_set(v___x_2532_, 0, v___x_2649_);
                        v___x_2651_ = v___x_2532_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
                        v___x_2651_ = v_reuseFailAlloc_2652_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2532_);
                    leanh::lean_inc(v_us_2490_);
                    v___x_2653_ = l_List_zipWith___at___00List_zip_spec__0(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_us_2490_,
                        v_us_2522_,
                    );
                    v___x_2654_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(v___x_2653_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
                    if leanh::lean_obj_tag(v___x_2654_) == 0 {
                        v_a_2655_ = leanh::lean_ctor_get(v___x_2654_, 0);
                        v_isSharedCheck_2685_ =
                            (!leanh::lean_is_exclusive(v___x_2654_)) as u8;
                        if v_isSharedCheck_2685_ == 0 {
                            v___x_2657_ = v___x_2654_;
                            v_isShared_2658_ = v_isSharedCheck_2685_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2655_);
                            leanh::lean_dec(v___x_2654_);
                            v___x_2657_ = leanh::lean_box(0);
                            v_isShared_2658_ = v_isSharedCheck_2685_;
                            state = 26;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2548_);
                        leanh::lean_dec_ref(v___x_2545_);
                        leanh::lean_dec(v_induct_2535_);
                        leanh::lean_dec(v_declName_2521_);
                        leanh::lean_dec(v_us_2490_);
                        leanh::lean_dec(v_declName_2489_);
                        leanh::lean_dec_ref(v_x_2470_);
                        leanh::lean_dec_ref(v_b_2468_);
                        leanh::lean_dec_ref(v_a_2467_);
                        leanh::lean_dec_ref(v_args_u2081_2466_);
                        v_a_2686_ = leanh::lean_ctor_get(v___x_2654_, 0);
                        v_isSharedCheck_2693_ =
                            (!leanh::lean_is_exclusive(v___x_2654_)) as u8;
                        if v_isSharedCheck_2693_ == 0 {
                            v___x_2688_ = v___x_2654_;
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 32;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2686_);
                            leanh::lean_dec(v___x_2654_);
                            v___x_2688_ = leanh::lean_box(0);
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            25 => {
                return v___x_2651_;
            }
            26 => {
                v___x_2659_ = (leanh::lean_unbox(v_a_2655_) as u8);
                leanh::lean_dec(v_a_2655_);
                if v___x_2659_ == 0 {
                    leanh::lean_dec_ref(v___x_2548_);
                    leanh::lean_dec_ref(v___x_2545_);
                    leanh::lean_dec(v_induct_2535_);
                    leanh::lean_dec(v_declName_2521_);
                    leanh::lean_dec(v_us_2490_);
                    leanh::lean_dec(v_declName_2489_);
                    leanh::lean_dec_ref(v_x_2470_);
                    leanh::lean_dec_ref(v_b_2468_);
                    leanh::lean_dec_ref(v_a_2467_);
                    leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2660_ = leanh::lean_box(0);
                    if v_isShared_2658_ == 0 {
                        leanh::lean_ctor_set(v___x_2657_, 0, v___x_2660_);
                        v___x_2662_ = v___x_2657_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2663_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
                        v___x_2662_ = v_reuseFailAlloc_2663_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2657_);
                    v___x_2664_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2467_, v___y_2472_);
                    if leanh::lean_obj_tag(v___x_2664_) == 0 {
                        v_a_2665_ = leanh::lean_ctor_get(v___x_2664_, 0);
                        leanh::lean_inc(v_a_2665_);
                        leanh::lean_dec_ref_known(v___x_2664_, 1);
                        v___x_2666_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_b_2468_, v___y_2472_);
                        if leanh::lean_obj_tag(v___x_2666_) == 0 {
                            v_a_2667_ = leanh::lean_ctor_get(v___x_2666_, 0);
                            leanh::lean_inc(v_a_2667_);
                            leanh::lean_dec_ref_known(v___x_2666_, 1);
                            v___x_2668_ = lean_nat_dec_le(v_a_2665_, v_a_2667_);
                            if v___x_2668_ == 0 {
                                leanh::lean_dec(v_a_2667_);
                                v___y_2550_ = v_a_2665_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_2665_);
                                v___y_2550_ = v_a_2667_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2665_);
                            leanh::lean_dec_ref(v___x_2548_);
                            leanh::lean_dec_ref(v___x_2545_);
                            leanh::lean_dec(v_induct_2535_);
                            leanh::lean_dec(v_declName_2521_);
                            leanh::lean_dec(v_us_2490_);
                            leanh::lean_dec(v_declName_2489_);
                            leanh::lean_dec_ref(v_x_2470_);
                            leanh::lean_dec_ref(v_b_2468_);
                            leanh::lean_dec_ref(v_a_2467_);
                            leanh::lean_dec_ref(v_args_u2081_2466_);
                            v_a_2669_ = leanh::lean_ctor_get(v___x_2666_, 0);
                            v_isSharedCheck_2676_ =
                                (!leanh::lean_is_exclusive(v___x_2666_)) as u8;
                            if v_isSharedCheck_2676_ == 0 {
                                v___x_2671_ = v___x_2666_;
                                v_isShared_2672_ = v_isSharedCheck_2676_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2669_);
                                leanh::lean_dec(v___x_2666_);
                                v___x_2671_ = leanh::lean_box(0);
                                v_isShared_2672_ = v_isSharedCheck_2676_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2548_);
                        leanh::lean_dec_ref(v___x_2545_);
                        leanh::lean_dec(v_induct_2535_);
                        leanh::lean_dec(v_declName_2521_);
                        leanh::lean_dec(v_us_2490_);
                        leanh::lean_dec(v_declName_2489_);
                        leanh::lean_dec_ref(v_x_2470_);
                        leanh::lean_dec_ref(v_b_2468_);
                        leanh::lean_dec_ref(v_a_2467_);
                        leanh::lean_dec_ref(v_args_u2081_2466_);
                        v_a_2677_ = leanh::lean_ctor_get(v___x_2664_, 0);
                        v_isSharedCheck_2684_ =
                            (!leanh::lean_is_exclusive(v___x_2664_)) as u8;
                        if v_isSharedCheck_2684_ == 0 {
                            v___x_2679_ = v___x_2664_;
                            v_isShared_2680_ = v_isSharedCheck_2684_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2677_);
                            leanh::lean_dec(v___x_2664_);
                            v___x_2679_ = leanh::lean_box(0);
                            v_isShared_2680_ = v_isSharedCheck_2684_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            27 => {
                return v___x_2662_;
            }
            28 => {
                if v_isShared_2672_ == 0 {
                    v___x_2674_ = v___x_2671_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
                    v___x_2674_ = v_reuseFailAlloc_2675_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2674_;
            }
            30 => {
                if v_isShared_2680_ == 0 {
                    v___x_2682_ = v___x_2679_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
                    v___x_2682_ = v_reuseFailAlloc_2683_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2682_;
            }
            32 => {
                if v_isShared_2689_ == 0 {
                    v___x_2691_ = v___x_2688_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
                    v___x_2691_ = v_reuseFailAlloc_2692_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2691_;
            }
            34 => {
                return v___x_2701_;
            }
            35 => {
                return v___x_2705_;
            }
            36 => {
                if v_isShared_2711_ == 0 {
                    v___x_2713_ = v___x_2710_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
                    v___x_2713_ = v_reuseFailAlloc_2714_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2713_;
            }
            38 => {
                return v___x_2718_;
            }
            39 => {
                if v_isShared_2724_ == 0 {
                    v___x_2726_ = v___x_2723_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctor_u2081_2733_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_args_u2081_2734_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_2735_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_b_2736_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_x_2737_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_x_2738_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_x_2739_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_2740_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_2741_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_2742_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_2743_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_2744_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_2745_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_2746_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_2747_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_2748_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_2749_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_2750_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(v_ctor_u2081_2733_, v_args_u2081_2734_, v_a_2735_, v_b_2736_, v_x_2737_, v_x_2738_, v_x_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
    leanh::lean_dec(v___y_2749_);
    leanh::lean_dec_ref(v___y_2748_);
    leanh::lean_dec(v___y_2747_);
    leanh::lean_dec_ref(v___y_2746_);
    leanh::lean_dec(v___y_2745_);
    leanh::lean_dec_ref(v___y_2744_);
    leanh::lean_dec(v___y_2743_);
    leanh::lean_dec_ref(v___y_2742_);
    leanh::lean_dec(v___y_2741_);
    leanh::lean_dec(v___y_2740_);
    return v_res_2751_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = leanh::lean_box(0);
    v_dummy_2753_ = l_Lean_Expr_sort___override(v___x_2752_);
    return v_dummy_2753_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2(
    mut v_b_2754_: *mut leanh::LeanObject,
    mut v_a_2755_: *mut leanh::LeanObject,
    mut v_x_2756_: *mut leanh::LeanObject,
    mut v_x_2757_: *mut leanh::LeanObject,
    mut v_x_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
    mut v___y_2760_: *mut leanh::LeanObject,
    mut v___y_2761_: *mut leanh::LeanObject,
    mut v___y_2762_: *mut leanh::LeanObject,
    mut v___y_2763_: *mut leanh::LeanObject,
    mut v___y_2764_: *mut leanh::LeanObject,
    mut v___y_2765_: *mut leanh::LeanObject,
    mut v___y_2766_: *mut leanh::LeanObject,
    mut v___y_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2756_) == 5 {
                    v_fn_2770_ = leanh::lean_ctor_get(v_x_2756_, 0);
                    leanh::lean_inc_ref(v_fn_2770_);
                    v_arg_2771_ = leanh::lean_ctor_get(v_x_2756_, 1);
                    leanh::lean_inc_ref(v_arg_2771_);
                    leanh::lean_dec_ref_known(v_x_2756_, 2);
                    v___x_2772_ = lean_array_set(v_x_2757_, v_x_2758_, v_arg_2771_);
                    v___x_2773_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2774_ = lean_nat_sub(v_x_2758_, v___x_2773_);
                    leanh::lean_dec(v_x_2758_);
                    v_x_2756_ = v_fn_2770_;
                    v_x_2757_ = v___x_2772_;
                    v_x_2758_ = v___x_2774_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_2758_);
                    v_dummy_2776_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0);
                    v_nargs_2777_ = l_Lean_Expr_getAppNumArgs(v_b_2754_);
                    leanh::lean_inc(v_nargs_2777_);
                    v___x_2778_ = lean_mk_array(v_nargs_2777_, v_dummy_2776_);
                    v___x_2779_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2780_ = lean_nat_sub(v_nargs_2777_, v___x_2779_);
                    leanh::lean_dec(v_nargs_2777_);
                    leanh::lean_inc_ref(v_b_2754_);
                    v___x_2781_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(v_x_2756_, v_x_2757_, v_a_2755_, v_b_2754_, v_b_2754_, v___x_2778_, v___x_2780_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
                    return v___x_2781_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___boxed(
    mut v_b_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v_x_2784_: *mut leanh::LeanObject,
    mut v_x_2785_: *mut leanh::LeanObject,
    mut v_x_2786_: *mut leanh::LeanObject,
    mut v___y_2787_: *mut leanh::LeanObject,
    mut v___y_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
    mut v___y_2791_: *mut leanh::LeanObject,
    mut v___y_2792_: *mut leanh::LeanObject,
    mut v___y_2793_: *mut leanh::LeanObject,
    mut v___y_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2(v_b_2782_, v_a_2783_, v_x_2784_, v_x_2785_, v_x_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
    leanh::lean_dec(v___y_2796_);
    leanh::lean_dec_ref(v___y_2795_);
    leanh::lean_dec(v___y_2794_);
    leanh::lean_dec_ref(v___y_2793_);
    leanh::lean_dec(v___y_2792_);
    leanh::lean_dec_ref(v___y_2791_);
    leanh::lean_dec(v___y_2790_);
    leanh::lean_dec_ref(v___y_2789_);
    leanh::lean_dec(v___y_2788_);
    leanh::lean_dec(v___y_2787_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2(
    mut v_a_2799_: *mut leanh::LeanObject,
    mut v_b_2800_: *mut leanh::LeanObject,
    mut v_x_2801_: *mut leanh::LeanObject,
    mut v_x_2802_: *mut leanh::LeanObject,
    mut v_x_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
    mut v___y_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
    mut v___y_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
    mut v___y_2813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2801_) == 5 {
        let mut v_fn_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_arg_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_fn_2815_ = leanh::lean_ctor_get(v_x_2801_, 0);
        leanh::lean_inc_ref(v_fn_2815_);
        v_arg_2816_ = leanh::lean_ctor_get(v_x_2801_, 1);
        leanh::lean_inc_ref(v_arg_2816_);
        leanh::lean_dec_ref_known(v_x_2801_, 2);
        v___x_2817_ = lean_array_set(v_x_2802_, v_x_2803_, v_arg_2816_);
        v___x_2818_ = leanh::lean_unsigned_to_nat(1);
        v___x_2819_ = lean_nat_sub(v_x_2803_, v___x_2818_);
        v___x_2820_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2(v_b_2800_, v_a_2799_, v_fn_2815_, v___x_2817_, v___x_2819_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
        return v___x_2820_;
    } else {
        let mut v_dummy_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_nargs_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_dummy_2821_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0);
        v_nargs_2822_ = l_Lean_Expr_getAppNumArgs(v_b_2800_);
        leanh::lean_inc(v_nargs_2822_);
        v___x_2823_ = lean_mk_array(v_nargs_2822_, v_dummy_2821_);
        v___x_2824_ = leanh::lean_unsigned_to_nat(1);
        v___x_2825_ = lean_nat_sub(v_nargs_2822_, v___x_2824_);
        leanh::lean_dec(v_nargs_2822_);
        leanh::lean_inc_ref(v_b_2800_);
        v___x_2826_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(v_x_2801_, v_x_2802_, v_a_2799_, v_b_2800_, v_b_2800_, v___x_2823_, v___x_2825_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
        return v___x_2826_;
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2___boxed(
    mut v_a_2827_: *mut leanh::LeanObject,
    mut v_b_2828_: *mut leanh::LeanObject,
    mut v_x_2829_: *mut leanh::LeanObject,
    mut v_x_2830_: *mut leanh::LeanObject,
    mut v_x_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
    mut v___y_2835_: *mut leanh::LeanObject,
    mut v___y_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2843_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2(v_a_2827_, v_b_2828_, v_x_2829_, v_x_2830_, v_x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
    leanh::lean_dec(v___y_2841_);
    leanh::lean_dec_ref(v___y_2840_);
    leanh::lean_dec(v___y_2839_);
    leanh::lean_dec_ref(v___y_2838_);
    leanh::lean_dec(v___y_2837_);
    leanh::lean_dec_ref(v___y_2836_);
    leanh::lean_dec(v___y_2835_);
    leanh::lean_dec_ref(v___y_2834_);
    leanh::lean_dec(v___y_2833_);
    leanh::lean_dec(v___y_2832_);
    leanh::lean_dec(v_x_2831_);
    return v_res_2843_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero(
    mut v_a_2844_: *mut leanh::LeanObject,
    mut v_b_2845_: *mut leanh::LeanObject,
    mut v_a_2846_: *mut leanh::LeanObject,
    mut v_a_2847_: *mut leanh::LeanObject,
    mut v_a_2848_: *mut leanh::LeanObject,
    mut v_a_2849_: *mut leanh::LeanObject,
    mut v_a_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dummy_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dummy_2857_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0);
    v_nargs_2858_ = l_Lean_Expr_getAppNumArgs(v_a_2844_);
    leanh::lean_inc(v_nargs_2858_);
    v___x_2859_ = lean_mk_array(v_nargs_2858_, v_dummy_2857_);
    v___x_2860_ = leanh::lean_unsigned_to_nat(1);
    v___x_2861_ = lean_nat_sub(v_nargs_2858_, v___x_2860_);
    leanh::lean_dec(v_nargs_2858_);
    leanh::lean_inc_ref(v_a_2844_);
    v___x_2862_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2(v_a_2844_, v_b_2845_, v_a_2844_, v___x_2859_, v___x_2861_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
    leanh::lean_dec(v___x_2861_);
    return v___x_2862_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero___boxed(
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v_b_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
    mut v_a_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
    mut v_a_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
    mut v_a_2873_: *mut leanh::LeanObject,
    mut v_a_2874_: *mut leanh::LeanObject,
    mut v_a_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2876_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero(
        v_a_2863_, v_b_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_,
        v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_,
    );
    leanh::lean_dec(v_a_2874_);
    leanh::lean_dec_ref(v_a_2873_);
    leanh::lean_dec(v_a_2872_);
    leanh::lean_dec_ref(v_a_2871_);
    leanh::lean_dec(v_a_2870_);
    leanh::lean_dec_ref(v_a_2869_);
    leanh::lean_dec(v_a_2868_);
    leanh::lean_dec_ref(v_a_2867_);
    leanh::lean_dec(v_a_2866_);
    leanh::lean_dec(v_a_2865_);
    return v_res_2876_;
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0(
    mut v_x_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: *mut leanh::LeanObject,
    mut v___y_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(v_x_2877_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    return v___x_2889_;
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___boxed(
    mut v_x_2890_: *mut leanh::LeanObject,
    mut v___y_2891_: *mut leanh::LeanObject,
    mut v___y_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0(v_x_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
    leanh::lean_dec(v___y_2900_);
    leanh::lean_dec_ref(v___y_2899_);
    leanh::lean_dec(v___y_2898_);
    leanh::lean_dec_ref(v___y_2897_);
    leanh::lean_dec(v___y_2896_);
    leanh::lean_dec_ref(v___y_2895_);
    leanh::lean_dec(v___y_2894_);
    leanh::lean_dec_ref(v___y_2893_);
    leanh::lean_dec(v___y_2892_);
    leanh::lean_dec(v___y_2891_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateCtor(
    mut v_a_2903_: *mut leanh::LeanObject,
    mut v_b_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
    mut v_a_2906_: *mut leanh::LeanObject,
    mut v_a_2907_: *mut leanh::LeanObject,
    mut v_a_2908_: *mut leanh::LeanObject,
    mut v_a_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_a_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut v_a_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_a_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_a_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2914_);
                leanh::lean_inc_ref(v_a_2913_);
                leanh::lean_inc(v_a_2912_);
                leanh::lean_inc_ref(v_a_2911_);
                leanh::lean_inc_ref(v_a_2903_);
                v___x_2916_ =
                    lean_infer_type(v_a_2903_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                if leanh::lean_obj_tag(v___x_2916_) == 0 {
                    v_a_2917_ = leanh::lean_ctor_get(v___x_2916_, 0);
                    leanh::lean_inc(v_a_2917_);
                    leanh::lean_dec_ref_known(v___x_2916_, 1);
                    v___x_2918_ =
                        l_Lean_Meta_whnfD(v_a_2917_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                    if leanh::lean_obj_tag(v___x_2918_) == 0 {
                        v_a_2919_ = leanh::lean_ctor_get(v___x_2918_, 0);
                        leanh::lean_inc(v_a_2919_);
                        leanh::lean_dec_ref_known(v___x_2918_, 1);
                        leanh::lean_inc(v_a_2914_);
                        leanh::lean_inc_ref(v_a_2913_);
                        leanh::lean_inc(v_a_2912_);
                        leanh::lean_inc_ref(v_a_2911_);
                        leanh::lean_inc_ref(v_b_2904_);
                        v___x_2920_ =
                            lean_infer_type(v_b_2904_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                        if leanh::lean_obj_tag(v___x_2920_) == 0 {
                            v_a_2921_ = leanh::lean_ctor_get(v___x_2920_, 0);
                            leanh::lean_inc(v_a_2921_);
                            leanh::lean_dec_ref_known(v___x_2920_, 1);
                            v___x_2922_ = l_Lean_Meta_whnfD(
                                v_a_2921_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_,
                            );
                            if leanh::lean_obj_tag(v___x_2922_) == 0 {
                                v_a_2923_ = leanh::lean_ctor_get(v___x_2922_, 0);
                                leanh::lean_inc(v_a_2923_);
                                leanh::lean_dec_ref_known(v___x_2922_, 1);
                                leanh::lean_inc(v_a_2919_);
                                v___x_2924_ = l_Lean_Meta_isDefEqD(
                                    v_a_2919_, v_a_2923_, v_a_2911_, v_a_2912_, v_a_2913_,
                                    v_a_2914_,
                                );
                                if leanh::lean_obj_tag(v___x_2924_) == 0 {
                                    v_a_2925_ = leanh::lean_ctor_get(v___x_2924_, 0);
                                    leanh::lean_inc(v_a_2925_);
                                    leanh::lean_dec_ref_known(v___x_2924_, 1);
                                    v___x_2926_ = (leanh::lean_unbox(v_a_2925_) as u8);
                                    leanh::lean_dec(v_a_2925_);
                                    if v___x_2926_ == 0 {
                                        leanh::lean_dec(v_a_2919_);
                                        v___x_2927_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero(v_a_2903_, v_b_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                                        return v___x_2927_;
                                    } else {
                                        v___x_2928_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo(v_a_2919_, v_a_2903_, v_b_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                                        leanh::lean_dec(v_a_2919_);
                                        return v___x_2928_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2919_);
                                    leanh::lean_dec_ref(v_b_2904_);
                                    leanh::lean_dec_ref(v_a_2903_);
                                    v_a_2929_ = leanh::lean_ctor_get(v___x_2924_, 0);
                                    v_isSharedCheck_2936_ =
                                        (!leanh::lean_is_exclusive(v___x_2924_)) as u8;
                                    if v_isSharedCheck_2936_ == 0 {
                                        v___x_2931_ = v___x_2924_;
                                        v_isShared_2932_ = v_isSharedCheck_2936_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2929_);
                                        leanh::lean_dec(v___x_2924_);
                                        v___x_2931_ = leanh::lean_box(0);
                                        v_isShared_2932_ = v_isSharedCheck_2936_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_2919_);
                                leanh::lean_dec_ref(v_b_2904_);
                                leanh::lean_dec_ref(v_a_2903_);
                                v_a_2937_ = leanh::lean_ctor_get(v___x_2922_, 0);
                                v_isSharedCheck_2944_ =
                                    (!leanh::lean_is_exclusive(v___x_2922_)) as u8;
                                if v_isSharedCheck_2944_ == 0 {
                                    v___x_2939_ = v___x_2922_;
                                    v_isShared_2940_ = v_isSharedCheck_2944_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2937_);
                                    leanh::lean_dec(v___x_2922_);
                                    v___x_2939_ = leanh::lean_box(0);
                                    v_isShared_2940_ = v_isSharedCheck_2944_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2919_);
                            leanh::lean_dec_ref(v_b_2904_);
                            leanh::lean_dec_ref(v_a_2903_);
                            v_a_2945_ = leanh::lean_ctor_get(v___x_2920_, 0);
                            v_isSharedCheck_2952_ =
                                (!leanh::lean_is_exclusive(v___x_2920_)) as u8;
                            if v_isSharedCheck_2952_ == 0 {
                                v___x_2947_ = v___x_2920_;
                                v_isShared_2948_ = v_isSharedCheck_2952_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2945_);
                                leanh::lean_dec(v___x_2920_);
                                v___x_2947_ = leanh::lean_box(0);
                                v_isShared_2948_ = v_isSharedCheck_2952_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2904_);
                        leanh::lean_dec_ref(v_a_2903_);
                        v_a_2953_ = leanh::lean_ctor_get(v___x_2918_, 0);
                        v_isSharedCheck_2960_ =
                            (!leanh::lean_is_exclusive(v___x_2918_)) as u8;
                        if v_isSharedCheck_2960_ == 0 {
                            v___x_2955_ = v___x_2918_;
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2953_);
                            leanh::lean_dec(v___x_2918_);
                            v___x_2955_ = leanh::lean_box(0);
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_2904_);
                    leanh::lean_dec_ref(v_a_2903_);
                    v_a_2961_ = leanh::lean_ctor_get(v___x_2916_, 0);
                    v_isSharedCheck_2968_ = (!leanh::lean_is_exclusive(v___x_2916_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v___x_2963_ = v___x_2916_;
                        v_isShared_2964_ = v_isSharedCheck_2968_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2961_);
                        leanh::lean_dec(v___x_2916_);
                        v___x_2963_ = leanh::lean_box(0);
                        v_isShared_2964_ = v_isSharedCheck_2968_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2932_ == 0 {
                    v___x_2934_ = v___x_2931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2935_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
                    v___x_2934_ = v_reuseFailAlloc_2935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2934_;
            }
            3 => {
                if v_isShared_2940_ == 0 {
                    v___x_2942_ = v___x_2939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
                    v___x_2942_ = v_reuseFailAlloc_2943_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2942_;
            }
            5 => {
                if v_isShared_2948_ == 0 {
                    v___x_2950_ = v___x_2947_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
                    v___x_2950_ = v_reuseFailAlloc_2951_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2950_;
            }
            7 => {
                if v_isShared_2956_ == 0 {
                    v___x_2958_ = v___x_2955_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
                    v___x_2958_ = v_reuseFailAlloc_2959_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2958_;
            }
            9 => {
                if v_isShared_2964_ == 0 {
                    v___x_2966_ = v___x_2963_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
                    v___x_2966_ = v_reuseFailAlloc_2967_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateCtor___boxed(
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_b_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_a_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
    mut v_a_2974_: *mut leanh::LeanObject,
    mut v_a_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_a_2977_: *mut leanh::LeanObject,
    mut v_a_2978_: *mut leanh::LeanObject,
    mut v_a_2979_: *mut leanh::LeanObject,
    mut v_a_2980_: *mut leanh::LeanObject,
    mut v_a_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Lean_Meta_Grind_propagateCtor(
        v_a_2969_, v_b_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_,
        v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_,
    );
    leanh::lean_dec(v_a_2980_);
    leanh::lean_dec_ref(v_a_2979_);
    leanh::lean_dec(v_a_2978_);
    leanh::lean_dec_ref(v_a_2977_);
    leanh::lean_dec(v_a_2976_);
    leanh::lean_dec_ref(v_a_2975_);
    leanh::lean_dec(v_a_2974_);
    leanh::lean_dec_ref(v_a_2973_);
    leanh::lean_dec(v_a_2972_);
    leanh::lean_dec(v_a_2971_);
    return v_res_2982_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Injective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Ctor(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Ctor(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Injective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
}