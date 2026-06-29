// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Ctor
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Injective Lean.Meta.Tactic.Grind.Simp
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::{
    lean_grind_internalize, lean_grind_mk_eq_proof,
};
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 106, 101, 99, 116, 105, 118, 105, 116, 121, 32, 116, 104, 101, 111, 114, 101, 109, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__2_value) as *mut crate::leanh::LeanObject,9743492140944907313 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__4_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__6_value) as *mut crate::leanh::LeanObject,13589827700912665667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 111, 67, 111, 110, 102, 117, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1: u64 = 0;
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ =
        l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__0;
    v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(
    mut v_eqs_1504_: *mut crate::leanh::LeanObject,
    mut v_proof_1505_: *mut crate::leanh::LeanObject,
    mut v_generation_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1540_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v_arg_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v_arg_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1554_: u8 = 0;
    let mut v_arg_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_a_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_a_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v_a_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_a_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_eqs_1504_);
                v___x_1521_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_eqs_1504_, v_a_1514_);
                if crate::leanh::lean_obj_tag(v___x_1521_) == 0 {
                    v_a_1522_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                    crate::leanh::lean_inc(v_a_1522_);
                    crate::leanh::lean_dec_ref_known(v___x_1521_, 1);
                    v___x_1545_ = l_Lean_Expr_cleanupAnnotations(v_a_1522_);
                    v___x_1546_ = l_Lean_Expr_isApp(v___x_1545_);
                    if v___x_1546_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1545_);
                        crate::leanh::lean_dec(v_generation_1506_);
                        crate::leanh::lean_dec_ref(v_proof_1505_);
                        v___y_1524_ = v_a_1511_;
                        v___y_1525_ = v_a_1512_;
                        v___y_1526_ = v_a_1513_;
                        v___y_1527_ = v_a_1514_;
                        v___y_1528_ = v_a_1515_;
                        v___y_1529_ = v_a_1516_;
                        state = 2;
                        continue;
                    } else {
                        v_arg_1547_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1547_);
                        v___x_1548_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1545_);
                        v___x_1549_ = l_Lean_Expr_isApp(v___x_1548_);
                        if v___x_1549_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1548_);
                            crate::leanh::lean_dec_ref(v_arg_1547_);
                            crate::leanh::lean_dec(v_generation_1506_);
                            crate::leanh::lean_dec_ref(v_proof_1505_);
                            v___y_1524_ = v_a_1511_;
                            v___y_1525_ = v_a_1512_;
                            v___y_1526_ = v_a_1513_;
                            v___y_1527_ = v_a_1514_;
                            v___y_1528_ = v_a_1515_;
                            v___y_1529_ = v_a_1516_;
                            state = 2;
                            continue;
                        } else {
                            v_arg_1550_ = crate::leanh::lean_ctor_get(v___x_1548_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1550_);
                            v___x_1551_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1548_);
                            v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__3;
                            v___x_1553_ = l_Lean_Expr_isConstOf(v___x_1551_, v___x_1552_);
                            if v___x_1553_ == 0 {
                                v___x_1554_ = l_Lean_Expr_isApp(v___x_1551_);
                                if v___x_1554_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1551_);
                                    crate::leanh::lean_dec_ref(v_arg_1550_);
                                    crate::leanh::lean_dec_ref(v_arg_1547_);
                                    crate::leanh::lean_dec(v_generation_1506_);
                                    crate::leanh::lean_dec_ref(v_proof_1505_);
                                    v___y_1524_ = v_a_1511_;
                                    v___y_1525_ = v_a_1512_;
                                    v___y_1526_ = v_a_1513_;
                                    v___y_1527_ = v_a_1514_;
                                    v___y_1528_ = v_a_1515_;
                                    v___y_1529_ = v_a_1516_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_1555_ = crate::leanh::lean_ctor_get(v___x_1551_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_1555_);
                                    v___x_1556_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1551_);
                                    v___x_1557_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__5;
                                    v___x_1558_ = l_Lean_Expr_isConstOf(v___x_1556_, v___x_1557_);
                                    if v___x_1558_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_1550_);
                                        v___x_1559_ = l_Lean_Expr_isApp(v___x_1556_);
                                        if v___x_1559_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_1556_);
                                            crate::leanh::lean_dec_ref(v_arg_1555_);
                                            crate::leanh::lean_dec_ref(v_arg_1547_);
                                            crate::leanh::lean_dec(v_generation_1506_);
                                            crate::leanh::lean_dec_ref(v_proof_1505_);
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
                                            crate::leanh::lean_dec_ref(v___x_1560_);
                                            if v___x_1562_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_1555_);
                                                crate::leanh::lean_dec_ref(v_arg_1547_);
                                                crate::leanh::lean_dec(v_generation_1506_);
                                                crate::leanh::lean_dec_ref(v_proof_1505_);
                                                v___y_1524_ = v_a_1511_;
                                                v___y_1525_ = v_a_1512_;
                                                v___y_1526_ = v_a_1513_;
                                                v___y_1527_ = v_a_1514_;
                                                v___y_1528_ = v_a_1515_;
                                                v___y_1529_ = v_a_1516_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_eqs_1504_);
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
                                                if crate::leanh::lean_obj_tag(v___x_1563_) == 0 {
                                                    v_a_1564_ =
                                                        crate::leanh::lean_ctor_get(v___x_1563_, 0);
                                                    crate::leanh::lean_inc(v_a_1564_);
                                                    crate::leanh::lean_dec_ref_known(
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
                                                    if crate::leanh::lean_obj_tag(v___x_1565_) == 0
                                                    {
                                                        v_a_1566_ = crate::leanh::lean_ctor_get(
                                                            v___x_1565_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_1566_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_1565_,
                                                            1,
                                                        );
                                                        v___x_1567_ = crate::leanh::lean_box(0);
                                                        crate::leanh::lean_inc(v_a_1516_);
                                                        crate::leanh::lean_inc_ref(v_a_1515_);
                                                        crate::leanh::lean_inc(v_a_1514_);
                                                        crate::leanh::lean_inc_ref(v_a_1513_);
                                                        crate::leanh::lean_inc(v_a_1512_);
                                                        crate::leanh::lean_inc_ref(v_a_1511_);
                                                        crate::leanh::lean_inc(v_a_1510_);
                                                        crate::leanh::lean_inc_ref(v_a_1509_);
                                                        crate::leanh::lean_inc(v_a_1508_);
                                                        crate::leanh::lean_inc(v_a_1507_);
                                                        crate::leanh::lean_inc(v_generation_1506_);
                                                        crate::leanh::lean_inc(v_a_1564_);
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
                                                        if crate::leanh::lean_obj_tag(v___x_1568_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_1568_,
                                                                1,
                                                            );
                                                            crate::leanh::lean_inc(v_a_1516_);
                                                            crate::leanh::lean_inc_ref(v_a_1515_);
                                                            crate::leanh::lean_inc(v_a_1514_);
                                                            crate::leanh::lean_inc_ref(v_a_1513_);
                                                            crate::leanh::lean_inc(v_a_1512_);
                                                            crate::leanh::lean_inc_ref(v_a_1511_);
                                                            crate::leanh::lean_inc(v_a_1510_);
                                                            crate::leanh::lean_inc_ref(v_a_1509_);
                                                            crate::leanh::lean_inc(v_a_1508_);
                                                            crate::leanh::lean_inc(v_a_1507_);
                                                            crate::leanh::lean_inc(v_a_1566_);
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
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_1569_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_1569_,
                                                                    1,
                                                                );
                                                                crate::leanh::lean_inc(v_a_1566_);
                                                                crate::leanh::lean_inc(v_a_1564_);
                                                                v___x_1570_ = l_Lean_Meta_mkHEq(
                                                                    v_a_1564_, v_a_1566_,
                                                                    v_a_1513_, v_a_1514_,
                                                                    v_a_1515_, v_a_1516_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_1570_,
                                                                ) == 0
                                                                {
                                                                    v_a_1571_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1570_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_1571_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_1570_, 1);
                                                                    v___x_1572_ = l_Lean_Meta_mkExpectedPropHint(v_proof_1505_, v_a_1571_);
                                                                    v___x_1573_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1564_, v_a_1566_, v___x_1572_, v___x_1562_, v_a_1507_, v_a_1509_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
                                                                    return v___x_1573_;
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1566_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1564_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_proof_1505_,
                                                                    );
                                                                    v_a_1574_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1570_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1581_ = (!crate::leanh::lean_is_exclusive(v___x_1570_)) as u8;
                                                                    if v_isSharedCheck_1581_ == 0 {
                                                                        v___x_1576_ = v___x_1570_;
                                                                        v_isShared_1577_ =
                                                                            v_isSharedCheck_1581_;
                                                                        state = 5;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1574_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1570_,
                                                                        );
                                                                        v___x_1576_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1577_ =
                                                                            v_isSharedCheck_1581_;
                                                                        state = 5;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_1566_);
                                                                crate::leanh::lean_dec(v_a_1564_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_proof_1505_,
                                                                );
                                                                return v___x_1569_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_a_1566_);
                                                            crate::leanh::lean_dec(v_a_1564_);
                                                            crate::leanh::lean_dec(
                                                                v_generation_1506_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_proof_1505_,
                                                            );
                                                            return v___x_1568_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1564_);
                                                        crate::leanh::lean_dec(v_generation_1506_);
                                                        crate::leanh::lean_dec_ref(v_proof_1505_);
                                                        v_a_1582_ = crate::leanh::lean_ctor_get(
                                                            v___x_1565_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1589_ =
                                                            (!crate::leanh::lean_is_exclusive(
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
                                                            crate::leanh::lean_inc(v_a_1582_);
                                                            crate::leanh::lean_dec(v___x_1565_);
                                                            v___x_1584_ = crate::leanh::lean_box(0);
                                                            v_isShared_1585_ =
                                                                v_isSharedCheck_1589_;
                                                            state = 7;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_1547_);
                                                    crate::leanh::lean_dec(v_generation_1506_);
                                                    crate::leanh::lean_dec_ref(v_proof_1505_);
                                                    v_a_1590_ =
                                                        crate::leanh::lean_ctor_get(v___x_1563_, 0);
                                                    v_isSharedCheck_1597_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1563_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1597_ == 0 {
                                                        v___x_1592_ = v___x_1563_;
                                                        v_isShared_1593_ = v_isSharedCheck_1597_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1590_);
                                                        crate::leanh::lean_dec(v___x_1563_);
                                                        v___x_1592_ = crate::leanh::lean_box(0);
                                                        v_isShared_1593_ = v_isSharedCheck_1597_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1556_);
                                        crate::leanh::lean_dec_ref(v_arg_1555_);
                                        crate::leanh::lean_dec_ref(v_eqs_1504_);
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
                                        if crate::leanh::lean_obj_tag(v___x_1598_) == 0 {
                                            v_a_1599_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                                            crate::leanh::lean_inc(v_a_1599_);
                                            crate::leanh::lean_dec_ref_known(v___x_1598_, 1);
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
                                            if crate::leanh::lean_obj_tag(v___x_1600_) == 0 {
                                                v_a_1601_ =
                                                    crate::leanh::lean_ctor_get(v___x_1600_, 0);
                                                crate::leanh::lean_inc(v_a_1601_);
                                                crate::leanh::lean_dec_ref_known(v___x_1600_, 1);
                                                v___x_1602_ = crate::leanh::lean_box(0);
                                                crate::leanh::lean_inc(v_a_1516_);
                                                crate::leanh::lean_inc_ref(v_a_1515_);
                                                crate::leanh::lean_inc(v_a_1514_);
                                                crate::leanh::lean_inc_ref(v_a_1513_);
                                                crate::leanh::lean_inc(v_a_1512_);
                                                crate::leanh::lean_inc_ref(v_a_1511_);
                                                crate::leanh::lean_inc(v_a_1510_);
                                                crate::leanh::lean_inc_ref(v_a_1509_);
                                                crate::leanh::lean_inc(v_a_1508_);
                                                crate::leanh::lean_inc(v_a_1507_);
                                                crate::leanh::lean_inc(v_generation_1506_);
                                                crate::leanh::lean_inc(v_a_1599_);
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
                                                if crate::leanh::lean_obj_tag(v___x_1603_) == 0 {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1603_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_inc(v_a_1516_);
                                                    crate::leanh::lean_inc_ref(v_a_1515_);
                                                    crate::leanh::lean_inc(v_a_1514_);
                                                    crate::leanh::lean_inc_ref(v_a_1513_);
                                                    crate::leanh::lean_inc(v_a_1512_);
                                                    crate::leanh::lean_inc_ref(v_a_1511_);
                                                    crate::leanh::lean_inc(v_a_1510_);
                                                    crate::leanh::lean_inc_ref(v_a_1509_);
                                                    crate::leanh::lean_inc(v_a_1508_);
                                                    crate::leanh::lean_inc(v_a_1507_);
                                                    crate::leanh::lean_inc(v_a_1601_);
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
                                                    if crate::leanh::lean_obj_tag(v___x_1604_) == 0
                                                    {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_1604_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc(v_a_1601_);
                                                        crate::leanh::lean_inc(v_a_1599_);
                                                        v___x_1605_ = l_Lean_Meta_mkEq(
                                                            v_a_1599_, v_a_1601_, v_a_1513_,
                                                            v_a_1514_, v_a_1515_, v_a_1516_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_1605_)
                                                            == 0
                                                        {
                                                            v_a_1606_ = crate::leanh::lean_ctor_get(
                                                                v___x_1605_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_1606_);
                                                            crate::leanh::lean_dec_ref_known(
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
                                                            crate::leanh::lean_dec(v_a_1601_);
                                                            crate::leanh::lean_dec(v_a_1599_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_proof_1505_,
                                                            );
                                                            v_a_1609_ = crate::leanh::lean_ctor_get(
                                                                v___x_1605_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1616_ =
                                                                (!crate::leanh::lean_is_exclusive(
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
                                                                crate::leanh::lean_inc(v_a_1609_);
                                                                crate::leanh::lean_dec(v___x_1605_);
                                                                v___x_1611_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1612_ =
                                                                    v_isSharedCheck_1616_;
                                                                state = 11;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1601_);
                                                        crate::leanh::lean_dec(v_a_1599_);
                                                        crate::leanh::lean_dec_ref(v_proof_1505_);
                                                        return v___x_1604_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_1601_);
                                                    crate::leanh::lean_dec(v_a_1599_);
                                                    crate::leanh::lean_dec(v_generation_1506_);
                                                    crate::leanh::lean_dec_ref(v_proof_1505_);
                                                    return v___x_1603_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_1599_);
                                                crate::leanh::lean_dec(v_generation_1506_);
                                                crate::leanh::lean_dec_ref(v_proof_1505_);
                                                v_a_1617_ =
                                                    crate::leanh::lean_ctor_get(v___x_1600_, 0);
                                                v_isSharedCheck_1624_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1600_))
                                                        as u8;
                                                if v_isSharedCheck_1624_ == 0 {
                                                    v___x_1619_ = v___x_1600_;
                                                    v_isShared_1620_ = v_isSharedCheck_1624_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1617_);
                                                    crate::leanh::lean_dec(v___x_1600_);
                                                    v___x_1619_ = crate::leanh::lean_box(0);
                                                    v_isShared_1620_ = v_isSharedCheck_1624_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_1547_);
                                            crate::leanh::lean_dec(v_generation_1506_);
                                            crate::leanh::lean_dec_ref(v_proof_1505_);
                                            v_a_1625_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                                            v_isSharedCheck_1632_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1598_))
                                                    as u8;
                                            if v_isSharedCheck_1632_ == 0 {
                                                v___x_1627_ = v___x_1598_;
                                                v_isShared_1628_ = v_isSharedCheck_1632_;
                                                state = 15;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1625_);
                                                crate::leanh::lean_dec(v___x_1598_);
                                                v___x_1627_ = crate::leanh::lean_box(0);
                                                v_isShared_1628_ = v_isSharedCheck_1632_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1551_);
                                crate::leanh::lean_dec_ref(v_eqs_1504_);
                                v___x_1633_ = crate::leanh::lean_unsigned_to_nat(0);
                                crate::leanh::lean_inc_ref(v_proof_1505_);
                                v___x_1634_ = l_Lean_Expr_proj___override(
                                    v___x_1552_,
                                    v___x_1633_,
                                    v_proof_1505_,
                                );
                                crate::leanh::lean_inc(v_generation_1506_);
                                v___x_1635_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(v_arg_1550_, v___x_1634_, v_generation_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
                                if crate::leanh::lean_obj_tag(v___x_1635_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1635_, 1);
                                    v___x_1636_ = crate::leanh::lean_unsigned_to_nat(1);
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
                                    crate::leanh::lean_dec_ref(v_arg_1547_);
                                    crate::leanh::lean_dec(v_generation_1506_);
                                    crate::leanh::lean_dec_ref(v_proof_1505_);
                                    return v___x_1635_;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_1506_);
                    crate::leanh::lean_dec_ref(v_proof_1505_);
                    crate::leanh::lean_dec_ref(v_eqs_1504_);
                    v_a_1639_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                    v_isSharedCheck_1646_ = (!crate::leanh::lean_is_exclusive(v___x_1521_)) as u8;
                    if v_isSharedCheck_1646_ == 0 {
                        v___x_1641_ = v___x_1521_;
                        v_isShared_1642_ = v_isSharedCheck_1646_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1639_);
                        crate::leanh::lean_dec(v___x_1521_);
                        v___x_1641_ = crate::leanh::lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1646_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1519_ = crate::leanh::lean_box(0);
                v___x_1520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                return v___x_1520_;
            }
            2 => {
                v___x_1530_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1524_);
                if crate::leanh::lean_obj_tag(v___x_1530_) == 0 {
                    v_a_1531_ = crate::leanh::lean_ctor_get(v___x_1530_, 0);
                    crate::leanh::lean_inc(v_a_1531_);
                    crate::leanh::lean_dec_ref_known(v___x_1530_, 1);
                    v___x_1532_ = (crate::leanh::lean_unbox(v_a_1531_) as u8);
                    crate::leanh::lean_dec(v_a_1531_);
                    if v___x_1532_ == 0 {
                        crate::leanh::lean_dec_ref(v_eqs_1504_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1533_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___closed__1);
                        v___x_1534_ = l_Lean_indentExpr(v_eqs_1504_);
                        v___x_1535_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1533_);
                        crate::leanh::lean_ctor_set(v___x_1535_, 1, v___x_1534_);
                        v___x_1536_ = l_Lean_Meta_Sym_reportIssue(
                            v___x_1535_,
                            v___y_1524_,
                            v___y_1525_,
                            v___y_1526_,
                            v___y_1527_,
                            v___y_1528_,
                            v___y_1529_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1536_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1536_, 1);
                            state = 1;
                            continue;
                        } else {
                            return v___x_1536_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_eqs_1504_);
                    v_a_1537_ = crate::leanh::lean_ctor_get(v___x_1530_, 0);
                    v_isSharedCheck_1544_ = (!crate::leanh::lean_is_exclusive(v___x_1530_)) as u8;
                    if v_isSharedCheck_1544_ == 0 {
                        v___x_1539_ = v___x_1530_;
                        v_isShared_1540_ = v_isSharedCheck_1544_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1537_);
                        crate::leanh::lean_dec(v___x_1530_);
                        v___x_1539_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
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
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
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
                    v_reuseFailAlloc_1588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
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
                    v_reuseFailAlloc_1596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
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
                    v_reuseFailAlloc_1615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
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
                    v_reuseFailAlloc_1623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
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
                    v_reuseFailAlloc_1631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
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
                    v_reuseFailAlloc_1645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
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
    mut v_eqs_1647_: *mut crate::leanh::LeanObject,
    mut v_proof_1648_: *mut crate::leanh::LeanObject,
    mut v_generation_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
    mut v_a_1655_: *mut crate::leanh::LeanObject,
    mut v_a_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1659_);
    crate::leanh::lean_dec_ref(v_a_1658_);
    crate::leanh::lean_dec(v_a_1657_);
    crate::leanh::lean_dec_ref(v_a_1656_);
    crate::leanh::lean_dec(v_a_1655_);
    crate::leanh::lean_dec_ref(v_a_1654_);
    crate::leanh::lean_dec(v_a_1653_);
    crate::leanh::lean_dec_ref(v_a_1652_);
    crate::leanh::lean_dec(v_a_1651_);
    crate::leanh::lean_dec(v_a_1650_);
    return v_res_1661_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = lean_st_ref_get(v___y_1666_);
    v_env_1669_ = crate::leanh::lean_ctor_get(v___x_1668_, 0);
    crate::leanh::lean_inc_ref(v_env_1669_);
    crate::leanh::lean_dec(v___x_1668_);
    v___x_1670_ = lean_st_ref_get(v___y_1664_);
    v_mctx_1671_ = crate::leanh::lean_ctor_get(v___x_1670_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1671_);
    crate::leanh::lean_dec(v___x_1670_);
    v_lctx_1672_ = crate::leanh::lean_ctor_get(v___y_1663_, 2);
    v_options_1673_ = crate::leanh::lean_ctor_get(v___y_1665_, 2);
    crate::leanh::lean_inc_ref(v_options_1673_);
    crate::leanh::lean_inc_ref(v_lctx_1672_);
    v___x_1674_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1674_, 0, v_env_1669_);
    crate::leanh::lean_ctor_set(v___x_1674_, 1, v_mctx_1671_);
    crate::leanh::lean_ctor_set(v___x_1674_, 2, v_lctx_1672_);
    crate::leanh::lean_ctor_set(v___x_1674_, 3, v_options_1673_);
    v___x_1675_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    crate::leanh::lean_ctor_set(v___x_1675_, 1, v_msgData_1662_);
    v___x_1676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1676_, 0, v___x_1675_);
    return v___x_1676_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    crate::leanh::lean_dec(v___y_1681_);
    crate::leanh::lean_dec_ref(v___y_1680_);
    crate::leanh::lean_dec(v___y_1679_);
    crate::leanh::lean_dec_ref(v___y_1678_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1690_ = crate::leanh::lean_ctor_get(v___y_1687_, 5);
                v___x_1691_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
                v_a_1692_ = crate::leanh::lean_ctor_get(v___x_1691_, 0);
                v_isSharedCheck_1700_ = (!crate::leanh::lean_is_exclusive(v___x_1691_)) as u8;
                if v_isSharedCheck_1700_ == 0 {
                    v___x_1694_ = v___x_1691_;
                    v_isShared_1695_ = v_isSharedCheck_1700_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1692_);
                    crate::leanh::lean_dec(v___x_1691_);
                    v___x_1694_ = crate::leanh::lean_box(0);
                    v_isShared_1695_ = v_isSharedCheck_1700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1690_);
                v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1696_, 0, v_ref_1690_);
                crate::leanh::lean_ctor_set(v___x_1696_, 1, v_a_1692_);
                if v_isShared_1695_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1694_, 1);
                    crate::leanh::lean_ctor_set(v___x_1694_, 0, v___x_1696_);
                    v___x_1698_ = v___x_1694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
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
    mut v_msg_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
    crate::leanh::lean_dec(v___y_1705_);
    crate::leanh::lean_dec_ref(v___y_1704_);
    crate::leanh::lean_dec(v___y_1703_);
    crate::leanh::lean_dec_ref(v___y_1702_);
    return v_res_1707_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1708_: *mut crate::leanh::LeanObject,
    mut v_msg_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1733_: u8 = 0;
    let mut v_cancelTk_x3f_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1735_: u8 = 0;
    let mut v_inheritedTraceOptions_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1721_ = crate::leanh::lean_ctor_get(v___y_1718_, 0);
    v_fileMap_1722_ = crate::leanh::lean_ctor_get(v___y_1718_, 1);
    v_options_1723_ = crate::leanh::lean_ctor_get(v___y_1718_, 2);
    v_currRecDepth_1724_ = crate::leanh::lean_ctor_get(v___y_1718_, 3);
    v_maxRecDepth_1725_ = crate::leanh::lean_ctor_get(v___y_1718_, 4);
    v_ref_1726_ = crate::leanh::lean_ctor_get(v___y_1718_, 5);
    v_currNamespace_1727_ = crate::leanh::lean_ctor_get(v___y_1718_, 6);
    v_openDecls_1728_ = crate::leanh::lean_ctor_get(v___y_1718_, 7);
    v_initHeartbeats_1729_ = crate::leanh::lean_ctor_get(v___y_1718_, 8);
    v_maxHeartbeats_1730_ = crate::leanh::lean_ctor_get(v___y_1718_, 9);
    v_quotContext_1731_ = crate::leanh::lean_ctor_get(v___y_1718_, 10);
    v_currMacroScope_1732_ = crate::leanh::lean_ctor_get(v___y_1718_, 11);
    v_diag_1733_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1718_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1734_ = crate::leanh::lean_ctor_get(v___y_1718_, 12);
    v_suppressElabErrors_1735_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1718_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1736_ = crate::leanh::lean_ctor_get(v___y_1718_, 13);
    v_ref_1737_ = l_Lean_replaceRef(v_ref_1708_, v_ref_1726_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1736_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1734_);
    crate::leanh::lean_inc(v_currMacroScope_1732_);
    crate::leanh::lean_inc(v_quotContext_1731_);
    crate::leanh::lean_inc(v_maxHeartbeats_1730_);
    crate::leanh::lean_inc(v_initHeartbeats_1729_);
    crate::leanh::lean_inc(v_openDecls_1728_);
    crate::leanh::lean_inc(v_currNamespace_1727_);
    crate::leanh::lean_inc(v_maxRecDepth_1725_);
    crate::leanh::lean_inc(v_currRecDepth_1724_);
    crate::leanh::lean_inc_ref(v_options_1723_);
    crate::leanh::lean_inc_ref(v_fileMap_1722_);
    crate::leanh::lean_inc_ref(v_fileName_1721_);
    v___x_1738_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1738_, 0, v_fileName_1721_);
    crate::leanh::lean_ctor_set(v___x_1738_, 1, v_fileMap_1722_);
    crate::leanh::lean_ctor_set(v___x_1738_, 2, v_options_1723_);
    crate::leanh::lean_ctor_set(v___x_1738_, 3, v_currRecDepth_1724_);
    crate::leanh::lean_ctor_set(v___x_1738_, 4, v_maxRecDepth_1725_);
    crate::leanh::lean_ctor_set(v___x_1738_, 5, v_ref_1737_);
    crate::leanh::lean_ctor_set(v___x_1738_, 6, v_currNamespace_1727_);
    crate::leanh::lean_ctor_set(v___x_1738_, 7, v_openDecls_1728_);
    crate::leanh::lean_ctor_set(v___x_1738_, 8, v_initHeartbeats_1729_);
    crate::leanh::lean_ctor_set(v___x_1738_, 9, v_maxHeartbeats_1730_);
    crate::leanh::lean_ctor_set(v___x_1738_, 10, v_quotContext_1731_);
    crate::leanh::lean_ctor_set(v___x_1738_, 11, v_currMacroScope_1732_);
    crate::leanh::lean_ctor_set(v___x_1738_, 12, v_cancelTk_x3f_1734_);
    crate::leanh::lean_ctor_set(v___x_1738_, 13, v_inheritedTraceOptions_1736_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1738_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1733_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1738_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1735_,
    );
    v___x_1739_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1709_, v___y_1716_, v___y_1717_, v___x_1738_, v___y_1719_);
    crate::leanh::lean_dec_ref_known(v___x_1738_, 14);
    return v___x_1739_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1740_: *mut crate::leanh::LeanObject,
    mut v_msg_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
    mut v___y_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1740_, v_msg_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
    crate::leanh::lean_dec(v___y_1751_);
    crate::leanh::lean_dec_ref(v___y_1750_);
    crate::leanh::lean_dec(v___y_1749_);
    crate::leanh::lean_dec_ref(v___y_1748_);
    crate::leanh::lean_dec(v___y_1747_);
    crate::leanh::lean_dec_ref(v___y_1746_);
    crate::leanh::lean_dec(v___y_1745_);
    crate::leanh::lean_dec_ref(v___y_1744_);
    crate::leanh::lean_dec(v___y_1743_);
    crate::leanh::lean_dec(v___y_1742_);
    crate::leanh::lean_dec(v_ref_1740_);
    return v_res_1753_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_1756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1758_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1759_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1759_, 1, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1759_, 2, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1759_, 3, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1759_, 4, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1759_, 5, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1759_, 6, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1759_, 7, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1759_, 8, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1759_, 9, v___x_1757_);
    return v___x_1759_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1760_);
    v___x_1762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1761_);
    return v___x_1762_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: usize = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = 5usize;
    v___x_1764_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1765_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
    v___x_1767_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_1768_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1767_);
    crate::leanh::lean_ctor_set(v___x_1768_, 1, v___x_1766_);
    crate::leanh::lean_ctor_set(v___x_1768_, 2, v___x_1764_);
    crate::leanh::lean_ctor_set(v___x_1768_, 3, v___x_1764_);
    crate::leanh::lean_ctor_set_usize(v___x_1768_, 4, v___x_1763_);
    return v___x_1768_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ = crate::leanh::lean_box(1);
    v___x_1770_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1771_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1772_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    crate::leanh::lean_ctor_set(v___x_1772_, 1, v___x_1770_);
    crate::leanh::lean_ctor_set(v___x_1772_, 2, v___x_1769_);
    return v___x_1772_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
    return v___x_1781_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
    return v___x_1784_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
    return v___x_1787_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
    return v___x_1790_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1794_: *mut crate::leanh::LeanObject,
    mut v_declHint_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut v_isExporting_1801_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1798_ = lean_st_ref_get(v___y_1796_);
                v_env_1799_ = crate::leanh::lean_ctor_get(v___x_1798_, 0);
                crate::leanh::lean_inc_ref(v_env_1799_);
                crate::leanh::lean_dec(v___x_1798_);
                v___x_1800_ = l_Lean_Name_isAnonymous(v_declHint_1795_);
                if v___x_1800_ == 0 {
                    v_isExporting_1801_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1799_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1801_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1799_);
                        crate::leanh::lean_dec(v_declHint_1795_);
                        v___x_1802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1802_, 0, v_msg_1794_);
                        return v___x_1802_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1799_);
                        v___x_1803_ = l_Lean_Environment_setExporting(v_env_1799_, v___x_1800_);
                        crate::leanh::lean_inc(v_declHint_1795_);
                        crate::leanh::lean_inc_ref(v___x_1803_);
                        v___x_1804_ = l_Lean_Environment_contains(
                            v___x_1803_,
                            v_declHint_1795_,
                            v_isExporting_1801_,
                        );
                        if v___x_1804_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1803_);
                            crate::leanh::lean_dec_ref(v_env_1799_);
                            crate::leanh::lean_dec(v_declHint_1795_);
                            v___x_1805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1805_, 0, v_msg_1794_);
                            return v___x_1805_;
                        } else {
                            v___x_1806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1807_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1808_ = l_Lean_Options_empty;
                            v___x_1809_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1809_, 0, v___x_1803_);
                            crate::leanh::lean_ctor_set(v___x_1809_, 1, v___x_1806_);
                            crate::leanh::lean_ctor_set(v___x_1809_, 2, v___x_1807_);
                            crate::leanh::lean_ctor_set(v___x_1809_, 3, v___x_1808_);
                            crate::leanh::lean_inc(v_declHint_1795_);
                            v___x_1810_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1795_, v___x_1800_);
                            v_c_1811_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1811_, 0, v___x_1809_);
                            crate::leanh::lean_ctor_set(v_c_1811_, 1, v___x_1810_);
                            v___x_1812_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1799_,
                                v_declHint_1795_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1812_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1799_);
                                crate::leanh::lean_dec(v_declHint_1795_);
                                v___x_1813_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1814_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1814_, 0, v___x_1813_);
                                crate::leanh::lean_ctor_set(v___x_1814_, 1, v_c_1811_);
                                v___x_1815_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1816_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1814_);
                                crate::leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
                                v___x_1817_ = l_Lean_MessageData_note(v___x_1816_);
                                v___x_1818_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1818_, 0, v_msg_1794_);
                                crate::leanh::lean_ctor_set(v___x_1818_, 1, v___x_1817_);
                                v___x_1819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
                                return v___x_1819_;
                            } else {
                                v_val_1820_ = crate::leanh::lean_ctor_get(v___x_1812_, 0);
                                v_isSharedCheck_1855_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1812_)) as u8;
                                if v_isSharedCheck_1855_ == 0 {
                                    v___x_1822_ = v___x_1812_;
                                    v_isShared_1823_ = v_isSharedCheck_1855_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1820_);
                                    crate::leanh::lean_dec(v___x_1812_);
                                    v___x_1822_ = crate::leanh::lean_box(0);
                                    v_isShared_1823_ = v_isSharedCheck_1855_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1799_);
                    crate::leanh::lean_dec(v_declHint_1795_);
                    v___x_1856_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1856_, 0, v_msg_1794_);
                    return v___x_1856_;
                }
            }
            1 => {
                v___x_1824_ = crate::leanh::lean_box(0);
                v___x_1825_ = l_Lean_Environment_header(v_env_1799_);
                crate::leanh::lean_dec_ref(v_env_1799_);
                v___x_1826_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1825_);
                v_mod_1827_ = lean_array_get(v___x_1824_, v___x_1826_, v_val_1820_);
                crate::leanh::lean_dec(v_val_1820_);
                crate::leanh::lean_dec_ref(v___x_1826_);
                v___x_1828_ = l_Lean_isPrivateName(v_declHint_1795_);
                crate::leanh::lean_dec(v_declHint_1795_);
                if v___x_1828_ == 0 {
                    v___x_1829_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1830_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1829_);
                    crate::leanh::lean_ctor_set(v___x_1830_, 1, v_c_1811_);
                    v___x_1831_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1832_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1832_, 0, v___x_1830_);
                    crate::leanh::lean_ctor_set(v___x_1832_, 1, v___x_1831_);
                    v___x_1833_ = l_Lean_MessageData_ofName(v_mod_1827_);
                    v___x_1834_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1834_, 0, v___x_1832_);
                    crate::leanh::lean_ctor_set(v___x_1834_, 1, v___x_1833_);
                    v___x_1835_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1836_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1836_, 0, v___x_1834_);
                    crate::leanh::lean_ctor_set(v___x_1836_, 1, v___x_1835_);
                    v___x_1837_ = l_Lean_MessageData_note(v___x_1836_);
                    v___x_1838_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1838_, 0, v_msg_1794_);
                    crate::leanh::lean_ctor_set(v___x_1838_, 1, v___x_1837_);
                    if v_isShared_1823_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1822_, 0);
                        crate::leanh::lean_ctor_set(v___x_1822_, 0, v___x_1838_);
                        v___x_1840_ = v___x_1822_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1841_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
                        v___x_1840_ = v_reuseFailAlloc_1841_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1843_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1842_);
                    crate::leanh::lean_ctor_set(v___x_1843_, 1, v_c_1811_);
                    v___x_1844_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1845_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1845_, 0, v___x_1843_);
                    crate::leanh::lean_ctor_set(v___x_1845_, 1, v___x_1844_);
                    v___x_1846_ = l_Lean_MessageData_ofName(v_mod_1827_);
                    v___x_1847_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1847_, 0, v___x_1845_);
                    crate::leanh::lean_ctor_set(v___x_1847_, 1, v___x_1846_);
                    v___x_1848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1849_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1847_);
                    crate::leanh::lean_ctor_set(v___x_1849_, 1, v___x_1848_);
                    v___x_1850_ = l_Lean_MessageData_note(v___x_1849_);
                    v___x_1851_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1851_, 0, v_msg_1794_);
                    crate::leanh::lean_ctor_set(v___x_1851_, 1, v___x_1850_);
                    if v_isShared_1823_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1822_, 0);
                        crate::leanh::lean_ctor_set(v___x_1822_, 0, v___x_1851_);
                        v___x_1853_ = v___x_1822_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
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
    mut v_msg_1857_: *mut crate::leanh::LeanObject,
    mut v_declHint_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1857_, v_declHint_1858_, v___y_1859_);
    crate::leanh::lean_dec(v___y_1859_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1862_: *mut crate::leanh::LeanObject,
    mut v_declHint_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1862_, v_declHint_1863_, v___y_1873_);
                v_a_1876_ = crate::leanh::lean_ctor_get(v___x_1875_, 0);
                v_isSharedCheck_1885_ = (!crate::leanh::lean_is_exclusive(v___x_1875_)) as u8;
                if v_isSharedCheck_1885_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    v_isShared_1879_ = v_isSharedCheck_1885_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1876_);
                    crate::leanh::lean_dec(v___x_1875_);
                    v___x_1878_ = crate::leanh::lean_box(0);
                    v_isShared_1879_ = v_isSharedCheck_1885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1880_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1881_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1881_, 0, v___x_1880_);
                crate::leanh::lean_ctor_set(v___x_1881_, 1, v_a_1876_);
                if v_isShared_1879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1878_, 0, v___x_1881_);
                    v___x_1883_ = v___x_1878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
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
    mut v_msg_1886_: *mut crate::leanh::LeanObject,
    mut v_declHint_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
    mut v___y_1896_: *mut crate::leanh::LeanObject,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1886_, v_declHint_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
    crate::leanh::lean_dec(v___y_1897_);
    crate::leanh::lean_dec_ref(v___y_1896_);
    crate::leanh::lean_dec(v___y_1895_);
    crate::leanh::lean_dec_ref(v___y_1894_);
    crate::leanh::lean_dec(v___y_1893_);
    crate::leanh::lean_dec_ref(v___y_1892_);
    crate::leanh::lean_dec(v___y_1891_);
    crate::leanh::lean_dec_ref(v___y_1890_);
    crate::leanh::lean_dec(v___y_1889_);
    crate::leanh::lean_dec(v___y_1888_);
    return v_res_1899_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1900_: *mut crate::leanh::LeanObject,
    mut v_msg_1901_: *mut crate::leanh::LeanObject,
    mut v_declHint_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1901_, v_declHint_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    v_a_1915_ = crate::leanh::lean_ctor_get(v___x_1914_, 0);
    crate::leanh::lean_inc(v_a_1915_);
    crate::leanh::lean_dec_ref(v___x_1914_);
    v___x_1916_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1900_, v_a_1915_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1917_: *mut crate::leanh::LeanObject,
    mut v_msg_1918_: *mut crate::leanh::LeanObject,
    mut v_declHint_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1931_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1917_, v_msg_1918_, v_declHint_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
    crate::leanh::lean_dec(v___y_1929_);
    crate::leanh::lean_dec_ref(v___y_1928_);
    crate::leanh::lean_dec(v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1926_);
    crate::leanh::lean_dec(v___y_1925_);
    crate::leanh::lean_dec_ref(v___y_1924_);
    crate::leanh::lean_dec(v___y_1923_);
    crate::leanh::lean_dec_ref(v___y_1922_);
    crate::leanh::lean_dec(v___y_1921_);
    crate::leanh::lean_dec(v___y_1920_);
    crate::leanh::lean_dec(v_ref_1917_);
    return v_res_1931_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1938_: *mut crate::leanh::LeanObject,
    mut v_constName_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1952_ = 0;
    crate::leanh::lean_inc(v_constName_1939_);
    v___x_1953_ = l_Lean_MessageData_ofConstName(v_constName_1939_, v___x_1952_);
    v___x_1954_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1954_, 0, v___x_1951_);
    crate::leanh::lean_ctor_set(v___x_1954_, 1, v___x_1953_);
    v___x_1955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___x_1954_);
    crate::leanh::lean_ctor_set(v___x_1956_, 1, v___x_1955_);
    v___x_1957_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1938_, v___x_1956_, v_constName_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1958_: *mut crate::leanh::LeanObject,
    mut v_constName_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(v_ref_1958_, v_constName_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
    crate::leanh::lean_dec(v___y_1969_);
    crate::leanh::lean_dec_ref(v___y_1968_);
    crate::leanh::lean_dec(v___y_1967_);
    crate::leanh::lean_dec_ref(v___y_1966_);
    crate::leanh::lean_dec(v___y_1965_);
    crate::leanh::lean_dec_ref(v___y_1964_);
    crate::leanh::lean_dec(v___y_1963_);
    crate::leanh::lean_dec_ref(v___y_1962_);
    crate::leanh::lean_dec(v___y_1961_);
    crate::leanh::lean_dec(v___y_1960_);
    crate::leanh::lean_dec(v_ref_1958_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(
    mut v_constName_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
    mut v___y_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1984_ = crate::leanh::lean_ctor_get(v___y_1981_, 5);
    v___x_1985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(v_ref_1984_, v_constName_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
    return v___x_1985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg___boxed(
    mut v_constName_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(v_constName_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
    crate::leanh::lean_dec(v___y_1996_);
    crate::leanh::lean_dec_ref(v___y_1995_);
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    crate::leanh::lean_dec(v___y_1992_);
    crate::leanh::lean_dec_ref(v___y_1991_);
    crate::leanh::lean_dec(v___y_1990_);
    crate::leanh::lean_dec_ref(v___y_1989_);
    crate::leanh::lean_dec(v___y_1988_);
    crate::leanh::lean_dec(v___y_1987_);
    return v_res_1998_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(
    mut v_constName_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
    mut v___y_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = lean_st_ref_get(v___y_2009_);
                v_env_2012_ = crate::leanh::lean_ctor_get(v___x_2011_, 0);
                crate::leanh::lean_inc_ref(v_env_2012_);
                crate::leanh::lean_dec(v___x_2011_);
                v___x_2013_ = 0;
                crate::leanh::lean_inc(v_constName_1999_);
                v___x_2014_ =
                    l_Lean_Environment_find_x3f(v_env_2012_, v_constName_1999_, v___x_2013_);
                if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
                    v___x_2015_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(v_constName_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
                    return v___x_2015_;
                } else {
                    crate::leanh::lean_dec(v_constName_1999_);
                    v_val_2016_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                    v_isSharedCheck_2023_ = (!crate::leanh::lean_is_exclusive(v___x_2014_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v___x_2018_ = v___x_2014_;
                        v_isShared_2019_ = v_isSharedCheck_2023_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2016_);
                        crate::leanh::lean_dec(v___x_2014_);
                        v___x_2018_ = crate::leanh::lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2018_, 0);
                    v___x_2021_ = v___x_2018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_val_2016_);
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
    mut v_constName_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
    crate::leanh::lean_dec(v___y_2034_);
    crate::leanh::lean_dec_ref(v___y_2033_);
    crate::leanh::lean_dec(v___y_2032_);
    crate::leanh::lean_dec_ref(v___y_2031_);
    crate::leanh::lean_dec(v___y_2030_);
    crate::leanh::lean_dec_ref(v___y_2029_);
    crate::leanh::lean_dec(v___y_2028_);
    crate::leanh::lean_dec_ref(v___y_2027_);
    crate::leanh::lean_dec(v___y_2026_);
    crate::leanh::lean_dec(v___y_2025_);
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
    mut v_00_u03b1_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_b_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_a_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_a_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_ctor_u2081_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctor_u2082_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noConfusionDeclName_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_a_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2120_: u8 = 0;
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_a_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_injDeclName_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v_trackZetaDelta_2172_: u8 = 0;
    let mut v_zetaDeltaSet_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2179_: u8 = 0;
    let mut v_inTypeClassResolution_2180_: u8 = 0;
    let mut v_cacheInferType_2181_: u8 = 0;
    let mut v___x_2182_: u8 = 0;
    let mut v_config_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u64 = 0;
    let mut v___x_2186_: u64 = 0;
    let mut v___x_2187_: u64 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u64 = 0;
    let mut v___x_2197_: u64 = 0;
    let mut v_key_2198_: u64 = 0;
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2207_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_reuseFailAlloc_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut v_a_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2221_: u8 = 0;
    let mut v_a_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v_a_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ctor_u2081_2089_ = l_Lean_Expr_getAppFn(v_a_2041_);
                v_ctor_u2082_2090_ = l_Lean_Expr_getAppFn(v_b_2042_);
                v___x_2091_ = lean_expr_eqv(v_ctor_u2081_2089_, v_ctor_u2082_2090_);
                crate::leanh::lean_dec_ref(v_ctor_u2082_2090_);
                v___x_2092_ = 1;
                if v___x_2091_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctor_u2081_2089_);
                    v___x_2093_ = l_Lean_Expr_getAppFn(v_00_u03b1_2040_);
                    if crate::leanh::lean_obj_tag(v___x_2093_) == 4 {
                        v_declName_2094_ = crate::leanh::lean_ctor_get(v___x_2093_, 0);
                        crate::leanh::lean_inc(v_declName_2094_);
                        crate::leanh::lean_dec_ref_known(v___x_2093_, 2);
                        v___x_2095_ = lean_st_ref_get(v_a_2052_);
                        v_env_2096_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
                        crate::leanh::lean_inc_ref(v_env_2096_);
                        crate::leanh::lean_dec(v___x_2095_);
                        v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0;
                        v_noConfusionDeclName_2098_ =
                            l_Lean_Name_str___override(v_declName_2094_, v___x_2097_);
                        v___x_2099_ = l_Lean_Environment_contains(
                            v_env_2096_,
                            v_noConfusionDeclName_2098_,
                            v___x_2092_,
                        );
                        if v___x_2099_ == 0 {
                            crate::leanh::lean_dec_ref(v_b_2042_);
                            crate::leanh::lean_dec_ref(v_a_2041_);
                            v___x_2100_ = crate::leanh::lean_box(0);
                            v___x_2101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2100_);
                            return v___x_2101_;
                        } else {
                            v___x_2102_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2047_);
                            if crate::leanh::lean_obj_tag(v___x_2102_) == 0 {
                                v_a_2103_ = crate::leanh::lean_ctor_get(v___x_2102_, 0);
                                crate::leanh::lean_inc(v_a_2103_);
                                crate::leanh::lean_dec_ref_known(v___x_2102_, 1);
                                crate::leanh::lean_inc(v_a_2052_);
                                crate::leanh::lean_inc_ref(v_a_2051_);
                                crate::leanh::lean_inc(v_a_2050_);
                                crate::leanh::lean_inc_ref(v_a_2049_);
                                crate::leanh::lean_inc(v_a_2048_);
                                crate::leanh::lean_inc_ref(v_a_2047_);
                                crate::leanh::lean_inc(v_a_2046_);
                                crate::leanh::lean_inc_ref(v_a_2045_);
                                crate::leanh::lean_inc(v_a_2044_);
                                crate::leanh::lean_inc(v_a_2043_);
                                v___x_2104_ = lean_grind_mk_eq_proof(
                                    v_a_2041_, v_b_2042_, v_a_2043_, v_a_2044_, v_a_2045_,
                                    v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_,
                                    v_a_2051_, v_a_2052_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2104_) == 0 {
                                    v_a_2105_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                                    crate::leanh::lean_inc(v_a_2105_);
                                    crate::leanh::lean_dec_ref_known(v___x_2104_, 1);
                                    v___x_2106_ = l_Lean_Meta_mkNoConfusion(
                                        v_a_2103_, v_a_2105_, v_a_2049_, v_a_2050_, v_a_2051_,
                                        v_a_2052_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2106_) == 0 {
                                        v_a_2107_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                                        crate::leanh::lean_inc(v_a_2107_);
                                        crate::leanh::lean_dec_ref_known(v___x_2106_, 1);
                                        v___x_2108_ = l_Lean_Meta_Grind_closeGoal(
                                            v_a_2107_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_,
                                            v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_,
                                            v_a_2052_,
                                        );
                                        return v___x_2108_;
                                    } else {
                                        v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                                        v_isSharedCheck_2116_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2106_)) as u8;
                                        if v_isSharedCheck_2116_ == 0 {
                                            v___x_2111_ = v___x_2106_;
                                            v_isShared_2112_ = v_isSharedCheck_2116_;
                                            state = 8;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2109_);
                                            crate::leanh::lean_dec(v___x_2106_);
                                            v___x_2111_ = crate::leanh::lean_box(0);
                                            v_isShared_2112_ = v_isSharedCheck_2116_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2103_);
                                    v_a_2117_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                                    v_isSharedCheck_2124_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2104_)) as u8;
                                    if v_isSharedCheck_2124_ == 0 {
                                        v___x_2119_ = v___x_2104_;
                                        v_isShared_2120_ = v_isSharedCheck_2124_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2117_);
                                        crate::leanh::lean_dec(v___x_2104_);
                                        v___x_2119_ = crate::leanh::lean_box(0);
                                        v_isShared_2120_ = v_isSharedCheck_2124_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_b_2042_);
                                crate::leanh::lean_dec_ref(v_a_2041_);
                                v_a_2125_ = crate::leanh::lean_ctor_get(v___x_2102_, 0);
                                v_isSharedCheck_2132_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2102_)) as u8;
                                if v_isSharedCheck_2132_ == 0 {
                                    v___x_2127_ = v___x_2102_;
                                    v_isShared_2128_ = v_isSharedCheck_2132_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2125_);
                                    crate::leanh::lean_dec(v___x_2102_);
                                    v___x_2127_ = crate::leanh::lean_box(0);
                                    v_isShared_2128_ = v_isSharedCheck_2132_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2093_);
                        crate::leanh::lean_dec_ref(v_b_2042_);
                        crate::leanh::lean_dec_ref(v_a_2041_);
                        v___x_2133_ = crate::leanh::lean_box(0);
                        v___x_2134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2134_, 0, v___x_2133_);
                        return v___x_2134_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_ctor_u2081_2089_) == 4 {
                        v_declName_2135_ = crate::leanh::lean_ctor_get(v_ctor_u2081_2089_, 0);
                        crate::leanh::lean_inc(v_declName_2135_);
                        crate::leanh::lean_dec_ref_known(v_ctor_u2081_2089_, 2);
                        v___x_2136_ = lean_st_ref_get(v_a_2052_);
                        v_env_2137_ = crate::leanh::lean_ctor_get(v___x_2136_, 0);
                        crate::leanh::lean_inc_ref(v_env_2137_);
                        crate::leanh::lean_dec(v___x_2136_);
                        v_injDeclName_2138_ =
                            l_Lean_Meta_mkInjectiveTheoremNameFor(v_declName_2135_);
                        crate::leanh::lean_inc(v_injDeclName_2138_);
                        v___x_2139_ = l_Lean_Environment_contains(
                            v_env_2137_,
                            v_injDeclName_2138_,
                            v___x_2092_,
                        );
                        if v___x_2139_ == 0 {
                            crate::leanh::lean_dec(v_injDeclName_2138_);
                            crate::leanh::lean_dec_ref(v_b_2042_);
                            crate::leanh::lean_dec_ref(v_a_2041_);
                            v___x_2140_ = crate::leanh::lean_box(0);
                            v___x_2141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2140_);
                            return v___x_2141_;
                        } else {
                            crate::leanh::lean_inc(v_injDeclName_2138_);
                            v___x_2142_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_injDeclName_2138_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                            if crate::leanh::lean_obj_tag(v___x_2142_) == 0 {
                                v_a_2143_ = crate::leanh::lean_ctor_get(v___x_2142_, 0);
                                crate::leanh::lean_inc(v_a_2143_);
                                crate::leanh::lean_dec_ref_known(v___x_2142_, 1);
                                crate::leanh::lean_inc(v_a_2052_);
                                crate::leanh::lean_inc_ref(v_a_2051_);
                                crate::leanh::lean_inc(v_a_2050_);
                                crate::leanh::lean_inc_ref(v_a_2049_);
                                crate::leanh::lean_inc(v_a_2048_);
                                crate::leanh::lean_inc_ref(v_a_2047_);
                                crate::leanh::lean_inc(v_a_2046_);
                                crate::leanh::lean_inc_ref(v_a_2045_);
                                crate::leanh::lean_inc(v_a_2044_);
                                crate::leanh::lean_inc(v_a_2043_);
                                crate::leanh::lean_inc_ref(v_b_2042_);
                                crate::leanh::lean_inc_ref(v_a_2041_);
                                v___x_2144_ = lean_grind_mk_eq_proof(
                                    v_a_2041_, v_b_2042_, v_a_2043_, v_a_2044_, v_a_2045_,
                                    v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_,
                                    v_a_2051_, v_a_2052_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2144_) == 0 {
                                    v_a_2145_ = crate::leanh::lean_ctor_get(v___x_2144_, 0);
                                    crate::leanh::lean_inc(v_a_2145_);
                                    crate::leanh::lean_dec_ref_known(v___x_2144_, 1);
                                    crate::leanh::lean_inc_ref(v_b_2042_);
                                    crate::leanh::lean_inc_ref(v_a_2041_);
                                    v___x_2146_ = l_Lean_Meta_mkEq(
                                        v_a_2041_, v_b_2042_, v_a_2049_, v_a_2050_, v_a_2051_,
                                        v_a_2052_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2146_) == 0 {
                                        v_a_2147_ = crate::leanh::lean_ctor_get(v___x_2146_, 0);
                                        crate::leanh::lean_inc(v_a_2147_);
                                        crate::leanh::lean_dec_ref_known(v___x_2146_, 1);
                                        v___x_2148_ = l_Lean_Meta_mkExpectedTypeHint(
                                            v_a_2145_, v_a_2147_, v_a_2049_, v_a_2050_, v_a_2051_,
                                            v_a_2052_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2148_) == 0 {
                                            v_a_2149_ = crate::leanh::lean_ctor_get(v___x_2148_, 0);
                                            crate::leanh::lean_inc(v_a_2149_);
                                            crate::leanh::lean_dec_ref_known(v___x_2148_, 1);
                                            v___x_2150_ = l_Lean_Meta_Context_config(v_a_2049_);
                                            v_foApprox_2151_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                0 as u32,
                                            );
                                            v_ctxApprox_2152_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                1 as u32,
                                            );
                                            v_quasiPatternApprox_2153_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    2 as u32,
                                                );
                                            v_constApprox_2154_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                3 as u32,
                                            );
                                            v_isDefEqStuckEx_2155_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    4 as u32,
                                                );
                                            v_unificationHints_2156_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    5 as u32,
                                                );
                                            v_proofIrrelevance_2157_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    6 as u32,
                                                );
                                            v_assignSyntheticOpaque_2158_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    7 as u32,
                                                );
                                            v_offsetCnstrs_2159_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2150_,
                                                    8 as u32,
                                                );
                                            v_etaStruct_2160_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                10 as u32,
                                            );
                                            v_univApprox_2161_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                11 as u32,
                                            );
                                            v_iota_2162_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                12 as u32,
                                            );
                                            v_beta_2163_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                13 as u32,
                                            );
                                            v_proj_2164_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                14 as u32,
                                            );
                                            v_zeta_2165_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                15 as u32,
                                            );
                                            v_zetaDelta_2166_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                16 as u32,
                                            );
                                            v_zetaUnused_2167_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                17 as u32,
                                            );
                                            v_zetaHave_2168_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2150_,
                                                18 as u32,
                                            );
                                            v_isSharedCheck_2213_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2150_))
                                                    as u8;
                                            if v_isSharedCheck_2213_ == 0 {
                                                v___x_2170_ = v___x_2150_;
                                                v_isShared_2171_ = v_isSharedCheck_2213_;
                                                state = 14;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_2150_);
                                                v___x_2170_ = crate::leanh::lean_box(0);
                                                v_isShared_2171_ = v_isSharedCheck_2213_;
                                                state = 14;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_2143_);
                                            crate::leanh::lean_dec(v_injDeclName_2138_);
                                            crate::leanh::lean_dec_ref(v_b_2042_);
                                            crate::leanh::lean_dec_ref(v_a_2041_);
                                            v_a_2214_ = crate::leanh::lean_ctor_get(v___x_2148_, 0);
                                            v_isSharedCheck_2221_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2148_))
                                                    as u8;
                                            if v_isSharedCheck_2221_ == 0 {
                                                v___x_2216_ = v___x_2148_;
                                                v_isShared_2217_ = v_isSharedCheck_2221_;
                                                state = 18;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2214_);
                                                crate::leanh::lean_dec(v___x_2148_);
                                                v___x_2216_ = crate::leanh::lean_box(0);
                                                v_isShared_2217_ = v_isSharedCheck_2221_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2145_);
                                        crate::leanh::lean_dec(v_a_2143_);
                                        crate::leanh::lean_dec(v_injDeclName_2138_);
                                        crate::leanh::lean_dec_ref(v_b_2042_);
                                        crate::leanh::lean_dec_ref(v_a_2041_);
                                        v_a_2222_ = crate::leanh::lean_ctor_get(v___x_2146_, 0);
                                        v_isSharedCheck_2229_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2146_)) as u8;
                                        if v_isSharedCheck_2229_ == 0 {
                                            v___x_2224_ = v___x_2146_;
                                            v_isShared_2225_ = v_isSharedCheck_2229_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2222_);
                                            crate::leanh::lean_dec(v___x_2146_);
                                            v___x_2224_ = crate::leanh::lean_box(0);
                                            v_isShared_2225_ = v_isSharedCheck_2229_;
                                            state = 20;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2143_);
                                    crate::leanh::lean_dec(v_injDeclName_2138_);
                                    crate::leanh::lean_dec_ref(v_b_2042_);
                                    crate::leanh::lean_dec_ref(v_a_2041_);
                                    v_a_2230_ = crate::leanh::lean_ctor_get(v___x_2144_, 0);
                                    v_isSharedCheck_2237_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2144_)) as u8;
                                    if v_isSharedCheck_2237_ == 0 {
                                        v___x_2232_ = v___x_2144_;
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 22;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2230_);
                                        crate::leanh::lean_dec(v___x_2144_);
                                        v___x_2232_ = crate::leanh::lean_box(0);
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_injDeclName_2138_);
                                crate::leanh::lean_dec_ref(v_b_2042_);
                                crate::leanh::lean_dec_ref(v_a_2041_);
                                v_a_2238_ = crate::leanh::lean_ctor_get(v___x_2142_, 0);
                                v_isSharedCheck_2245_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2142_)) as u8;
                                if v_isSharedCheck_2245_ == 0 {
                                    v___x_2240_ = v___x_2142_;
                                    v_isShared_2241_ = v_isSharedCheck_2245_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2238_);
                                    crate::leanh::lean_dec(v___x_2142_);
                                    v___x_2240_ = crate::leanh::lean_box(0);
                                    v_isShared_2241_ = v_isSharedCheck_2245_;
                                    state = 24;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ctor_u2081_2089_);
                        crate::leanh::lean_dec_ref(v_b_2042_);
                        crate::leanh::lean_dec_ref(v_a_2041_);
                        v___x_2246_ = crate::leanh::lean_box(0);
                        v___x_2247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2247_, 0, v___x_2246_);
                        return v___x_2247_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2052_);
                crate::leanh::lean_inc_ref(v_a_2051_);
                crate::leanh::lean_inc(v_a_2050_);
                crate::leanh::lean_inc_ref(v_a_2049_);
                crate::leanh::lean_inc_ref(v_a_2055_);
                v___x_2056_ =
                    lean_infer_type(v_a_2055_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                if crate::leanh::lean_obj_tag(v___x_2056_) == 0 {
                    v_a_2057_ = crate::leanh::lean_ctor_get(v___x_2056_, 0);
                    crate::leanh::lean_inc(v_a_2057_);
                    crate::leanh::lean_dec_ref_known(v___x_2056_, 1);
                    v___x_2058_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2041_, v_a_2043_);
                    crate::leanh::lean_dec_ref(v_a_2041_);
                    if crate::leanh::lean_obj_tag(v___x_2058_) == 0 {
                        v_a_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                        crate::leanh::lean_inc(v_a_2059_);
                        crate::leanh::lean_dec_ref_known(v___x_2058_, 1);
                        v___x_2060_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_b_2042_, v_a_2043_);
                        crate::leanh::lean_dec_ref(v_b_2042_);
                        if crate::leanh::lean_obj_tag(v___x_2060_) == 0 {
                            v_a_2061_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                            crate::leanh::lean_inc(v_a_2061_);
                            crate::leanh::lean_dec_ref_known(v___x_2060_, 1);
                            v___x_2062_ = lean_nat_dec_le(v_a_2059_, v_a_2061_);
                            if v___x_2062_ == 0 {
                                crate::leanh::lean_dec(v_a_2061_);
                                v___x_2063_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(v_a_2057_, v_a_2055_, v_a_2059_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                                return v___x_2063_;
                            } else {
                                crate::leanh::lean_dec(v_a_2059_);
                                v___x_2064_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(v_a_2057_, v_a_2055_, v_a_2061_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
                                return v___x_2064_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2059_);
                            crate::leanh::lean_dec(v_a_2057_);
                            crate::leanh::lean_dec_ref(v_a_2055_);
                            v_a_2065_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                            v_isSharedCheck_2072_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2060_)) as u8;
                            if v_isSharedCheck_2072_ == 0 {
                                v___x_2067_ = v___x_2060_;
                                v_isShared_2068_ = v_isSharedCheck_2072_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2065_);
                                crate::leanh::lean_dec(v___x_2060_);
                                v___x_2067_ = crate::leanh::lean_box(0);
                                v_isShared_2068_ = v_isSharedCheck_2072_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2057_);
                        crate::leanh::lean_dec_ref(v_a_2055_);
                        crate::leanh::lean_dec_ref(v_b_2042_);
                        v_a_2073_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                        v_isSharedCheck_2080_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2058_)) as u8;
                        if v_isSharedCheck_2080_ == 0 {
                            v___x_2075_ = v___x_2058_;
                            v_isShared_2076_ = v_isSharedCheck_2080_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2073_);
                            crate::leanh::lean_dec(v___x_2058_);
                            v___x_2075_ = crate::leanh::lean_box(0);
                            v_isShared_2076_ = v_isSharedCheck_2080_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2055_);
                    crate::leanh::lean_dec_ref(v_b_2042_);
                    crate::leanh::lean_dec_ref(v_a_2041_);
                    v_a_2081_ = crate::leanh::lean_ctor_get(v___x_2056_, 0);
                    v_isSharedCheck_2088_ = (!crate::leanh::lean_is_exclusive(v___x_2056_)) as u8;
                    if v_isSharedCheck_2088_ == 0 {
                        v___x_2083_ = v___x_2056_;
                        v_isShared_2084_ = v_isSharedCheck_2088_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2081_);
                        crate::leanh::lean_dec(v___x_2056_);
                        v___x_2083_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
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
                    v_reuseFailAlloc_2079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
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
                    v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
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
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
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
                    v_reuseFailAlloc_2123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
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
                    v_reuseFailAlloc_2131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
                    v___x_2130_ = v_reuseFailAlloc_2131_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2130_;
            }
            14 => {
                v_trackZetaDelta_2172_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2173_ = crate::leanh::lean_ctor_get(v_a_2049_, 1);
                v_lctx_2174_ = crate::leanh::lean_ctor_get(v_a_2049_, 2);
                v_localInstances_2175_ = crate::leanh::lean_ctor_get(v_a_2049_, 3);
                v_defEqCtx_x3f_2176_ = crate::leanh::lean_ctor_get(v_a_2049_, 4);
                v_synthPendingDepth_2177_ = crate::leanh::lean_ctor_get(v_a_2049_, 5);
                v_canUnfold_x3f_2178_ = crate::leanh::lean_ctor_get(v_a_2049_, 6);
                v_univApprox_2179_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2180_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2181_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2182_ = 1;
                if v_isShared_2171_ == 0 {
                    v_config_2184_ = v___x_2170_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2212_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        0 as u32,
                        v_foApprox_2151_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        1 as u32,
                        v_ctxApprox_2152_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        2 as u32,
                        v_quasiPatternApprox_2153_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        3 as u32,
                        v_constApprox_2154_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        4 as u32,
                        v_isDefEqStuckEx_2155_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        5 as u32,
                        v_unificationHints_2156_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        6 as u32,
                        v_proofIrrelevance_2157_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        7 as u32,
                        v_assignSyntheticOpaque_2158_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        8 as u32,
                        v_offsetCnstrs_2159_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        10 as u32,
                        v_etaStruct_2160_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        11 as u32,
                        v_univApprox_2161_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        12 as u32,
                        v_iota_2162_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        13 as u32,
                        v_beta_2163_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        14 as u32,
                        v_proj_2164_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        15 as u32,
                        v_zeta_2165_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        16 as u32,
                        v_zetaDelta_2166_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2212_,
                        17 as u32,
                        v_zetaUnused_2167_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
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
                crate::leanh::lean_ctor_set_uint8(v_config_2184_, 9 as u32, v___x_2182_);
                v___x_2185_ = l_Lean_Meta_Context_configKey(v_a_2049_);
                v___x_2186_ = 3u64;
                v___x_2187_ = lean_uint64_shift_right(v___x_2185_, v___x_2186_);
                v___x_2188_ = l_Lean_ConstantInfo_type(v_a_2143_);
                crate::leanh::lean_dec(v_a_2143_);
                v___x_2189_ = l_Lean_Expr_getForallArity(v___x_2188_);
                v___x_2190_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_2189_);
                v___x_2191_ = lean_mk_array(v___x_2189_, v___x_2190_);
                v___x_2192_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2193_ = lean_nat_sub(v___x_2189_, v___x_2192_);
                crate::leanh::lean_dec(v___x_2189_);
                v___x_2194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2194_, 0, v_a_2149_);
                v___x_2195_ = lean_array_set(v___x_2191_, v___x_2193_, v___x_2194_);
                crate::leanh::lean_dec(v___x_2193_);
                v___x_2196_ = lean_uint64_shift_left(v___x_2187_, v___x_2186_);
                v___x_2197_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__1);
                v_key_2198_ = lean_uint64_lor(v___x_2196_, v___x_2197_);
                v___x_2199_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2199_, 0, v_config_2184_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2199_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2198_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2178_);
                crate::leanh::lean_inc(v_synthPendingDepth_2177_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2176_);
                crate::leanh::lean_inc_ref(v_localInstances_2175_);
                crate::leanh::lean_inc_ref(v_lctx_2174_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2173_);
                v___x_2200_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                crate::leanh::lean_ctor_set(v___x_2200_, 1, v_zetaDeltaSet_2173_);
                crate::leanh::lean_ctor_set(v___x_2200_, 2, v_lctx_2174_);
                crate::leanh::lean_ctor_set(v___x_2200_, 3, v_localInstances_2175_);
                crate::leanh::lean_ctor_set(v___x_2200_, 4, v_defEqCtx_x3f_2176_);
                crate::leanh::lean_ctor_set(v___x_2200_, 5, v_synthPendingDepth_2177_);
                crate::leanh::lean_ctor_set(v___x_2200_, 6, v_canUnfold_x3f_2178_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2172_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2179_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2180_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2200_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
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
                crate::leanh::lean_dec_ref_known(v___x_2200_, 7);
                if crate::leanh::lean_obj_tag(v___x_2201_) == 0 {
                    v_a_2202_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                    crate::leanh::lean_inc(v_a_2202_);
                    crate::leanh::lean_dec_ref_known(v___x_2201_, 1);
                    v_a_2055_ = v_a_2202_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2201_) == 0 {
                        v_a_2203_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                        crate::leanh::lean_inc(v_a_2203_);
                        crate::leanh::lean_dec_ref_known(v___x_2201_, 1);
                        v_a_2055_ = v_a_2203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2042_);
                        crate::leanh::lean_dec_ref(v_a_2041_);
                        v_a_2204_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                        v_isSharedCheck_2211_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2201_)) as u8;
                        if v_isSharedCheck_2211_ == 0 {
                            v___x_2206_ = v___x_2201_;
                            v_isShared_2207_ = v_isSharedCheck_2211_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2204_);
                            crate::leanh::lean_dec(v___x_2201_);
                            v___x_2206_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
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
                    v_reuseFailAlloc_2220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
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
                    v_reuseFailAlloc_2228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
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
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
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
                    v_reuseFailAlloc_2244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
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
    mut v_00_u03b1_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_b_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
    mut v_a_2255_: *mut crate::leanh::LeanObject,
    mut v_a_2256_: *mut crate::leanh::LeanObject,
    mut v_a_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2260_);
    crate::leanh::lean_dec_ref(v_a_2259_);
    crate::leanh::lean_dec(v_a_2258_);
    crate::leanh::lean_dec_ref(v_a_2257_);
    crate::leanh::lean_dec(v_a_2256_);
    crate::leanh::lean_dec_ref(v_a_2255_);
    crate::leanh::lean_dec(v_a_2254_);
    crate::leanh::lean_dec_ref(v_a_2253_);
    crate::leanh::lean_dec(v_a_2252_);
    crate::leanh::lean_dec(v_a_2251_);
    crate::leanh::lean_dec_ref(v_00_u03b1_2248_);
    return v_res_2262_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0(
    mut v_00_u03b1_2263_: *mut crate::leanh::LeanObject,
    mut v_constName_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___redArg(v_constName_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
    return v___x_2276_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0___boxed(
    mut v_00_u03b1_2277_: *mut crate::leanh::LeanObject,
    mut v_constName_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0(v_00_u03b1_2277_, v_constName_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
    crate::leanh::lean_dec(v___y_2288_);
    crate::leanh::lean_dec_ref(v___y_2287_);
    crate::leanh::lean_dec(v___y_2286_);
    crate::leanh::lean_dec_ref(v___y_2285_);
    crate::leanh::lean_dec(v___y_2284_);
    crate::leanh::lean_dec_ref(v___y_2283_);
    crate::leanh::lean_dec(v___y_2282_);
    crate::leanh::lean_dec_ref(v___y_2281_);
    crate::leanh::lean_dec(v___y_2280_);
    crate::leanh::lean_dec(v___y_2279_);
    return v_res_2290_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2291_: *mut crate::leanh::LeanObject,
    mut v_ref_2292_: *mut crate::leanh::LeanObject,
    mut v_constName_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___redArg(v_ref_2292_, v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
    return v___x_2305_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2306_: *mut crate::leanh::LeanObject,
    mut v_ref_2307_: *mut crate::leanh::LeanObject,
    mut v_constName_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1(v_00_u03b1_2306_, v_ref_2307_, v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
    crate::leanh::lean_dec(v___y_2318_);
    crate::leanh::lean_dec_ref(v___y_2317_);
    crate::leanh::lean_dec(v___y_2316_);
    crate::leanh::lean_dec_ref(v___y_2315_);
    crate::leanh::lean_dec(v___y_2314_);
    crate::leanh::lean_dec_ref(v___y_2313_);
    crate::leanh::lean_dec(v___y_2312_);
    crate::leanh::lean_dec_ref(v___y_2311_);
    crate::leanh::lean_dec(v___y_2310_);
    crate::leanh::lean_dec(v___y_2309_);
    crate::leanh::lean_dec(v_ref_2307_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_2321_: *mut crate::leanh::LeanObject,
    mut v_ref_2322_: *mut crate::leanh::LeanObject,
    mut v_msg_2323_: *mut crate::leanh::LeanObject,
    mut v_declHint_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2322_, v_msg_2323_, v_declHint_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_2337_: *mut crate::leanh::LeanObject,
    mut v_ref_2338_: *mut crate::leanh::LeanObject,
    mut v_msg_2339_: *mut crate::leanh::LeanObject,
    mut v_declHint_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
    mut v___y_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2337_, v_ref_2338_, v_msg_2339_, v_declHint_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
    crate::leanh::lean_dec(v___y_2350_);
    crate::leanh::lean_dec_ref(v___y_2349_);
    crate::leanh::lean_dec(v___y_2348_);
    crate::leanh::lean_dec_ref(v___y_2347_);
    crate::leanh::lean_dec(v___y_2346_);
    crate::leanh::lean_dec_ref(v___y_2345_);
    crate::leanh::lean_dec(v___y_2344_);
    crate::leanh::lean_dec_ref(v___y_2343_);
    crate::leanh::lean_dec(v___y_2342_);
    crate::leanh::lean_dec(v___y_2341_);
    crate::leanh::lean_dec(v_ref_2338_);
    return v_res_2352_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_2353_: *mut crate::leanh::LeanObject,
    mut v_declHint_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2353_, v_declHint_2354_, v___y_2364_);
    return v___x_2366_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_2367_: *mut crate::leanh::LeanObject,
    mut v_declHint_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2367_, v_declHint_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
    crate::leanh::lean_dec(v___y_2378_);
    crate::leanh::lean_dec_ref(v___y_2377_);
    crate::leanh::lean_dec(v___y_2376_);
    crate::leanh::lean_dec_ref(v___y_2375_);
    crate::leanh::lean_dec(v___y_2374_);
    crate::leanh::lean_dec_ref(v___y_2373_);
    crate::leanh::lean_dec(v___y_2372_);
    crate::leanh::lean_dec_ref(v___y_2371_);
    crate::leanh::lean_dec(v___y_2370_);
    crate::leanh::lean_dec(v___y_2369_);
    return v_res_2380_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_2381_: *mut crate::leanh::LeanObject,
    mut v_ref_2382_: *mut crate::leanh::LeanObject,
    mut v_msg_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2382_, v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    return v___x_2395_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_2396_: *mut crate::leanh::LeanObject,
    mut v_ref_2397_: *mut crate::leanh::LeanObject,
    mut v_msg_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2410_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2396_, v_ref_2397_, v_msg_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
    crate::leanh::lean_dec(v___y_2408_);
    crate::leanh::lean_dec_ref(v___y_2407_);
    crate::leanh::lean_dec(v___y_2406_);
    crate::leanh::lean_dec_ref(v___y_2405_);
    crate::leanh::lean_dec(v___y_2404_);
    crate::leanh::lean_dec_ref(v___y_2403_);
    crate::leanh::lean_dec(v___y_2402_);
    crate::leanh::lean_dec_ref(v___y_2401_);
    crate::leanh::lean_dec(v___y_2400_);
    crate::leanh::lean_dec(v___y_2399_);
    crate::leanh::lean_dec(v_ref_2397_);
    return v_res_2410_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_2411_: *mut crate::leanh::LeanObject,
    mut v_msg_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2412_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
    return v___x_2424_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2425_: *mut crate::leanh::LeanObject,
    mut v_msg_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2425_, v_msg_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
    crate::leanh::lean_dec(v___y_2436_);
    crate::leanh::lean_dec_ref(v___y_2435_);
    crate::leanh::lean_dec(v___y_2434_);
    crate::leanh::lean_dec_ref(v___y_2433_);
    crate::leanh::lean_dec(v___y_2432_);
    crate::leanh::lean_dec_ref(v___y_2431_);
    crate::leanh::lean_dec(v___y_2430_);
    crate::leanh::lean_dec_ref(v___y_2429_);
    crate::leanh::lean_dec(v___y_2428_);
    crate::leanh::lean_dec(v___y_2427_);
    return v_res_2438_;
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(
    mut v_x_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2439_) == 0 {
                    v___x_2445_ = 1;
                    v___x_2446_ = crate::leanh::lean_box((v___x_2445_) as usize);
                    v___x_2447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2447_, 0, v___x_2446_);
                    return v___x_2447_;
                } else {
                    v_head_2448_ = crate::leanh::lean_ctor_get(v_x_2439_, 0);
                    crate::leanh::lean_inc(v_head_2448_);
                    v_tail_2449_ = crate::leanh::lean_ctor_get(v_x_2439_, 1);
                    crate::leanh::lean_inc(v_tail_2449_);
                    crate::leanh::lean_dec_ref_known(v_x_2439_, 2);
                    v_fst_2450_ = crate::leanh::lean_ctor_get(v_head_2448_, 0);
                    crate::leanh::lean_inc(v_fst_2450_);
                    v_snd_2451_ = crate::leanh::lean_ctor_get(v_head_2448_, 1);
                    crate::leanh::lean_inc(v_snd_2451_);
                    crate::leanh::lean_dec(v_head_2448_);
                    v___x_2452_ = l_Lean_Meta_isLevelDefEq(
                        v_fst_2450_,
                        v_snd_2451_,
                        v___y_2440_,
                        v___y_2441_,
                        v___y_2442_,
                        v___y_2443_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2452_) == 0 {
                        v_a_2453_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
                        crate::leanh::lean_inc(v_a_2453_);
                        v___x_2454_ = (crate::leanh::lean_unbox(v_a_2453_) as u8);
                        crate::leanh::lean_dec(v_a_2453_);
                        if v___x_2454_ == 0 {
                            crate::leanh::lean_dec(v_tail_2449_);
                            return v___x_2452_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2452_, 1);
                            v_x_2439_ = v_tail_2449_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_2449_);
                        return v___x_2452_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg___boxed(
    mut v_x_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
    mut v___y_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(v_x_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
    crate::leanh::lean_dec(v___y_2460_);
    crate::leanh::lean_dec_ref(v___y_2459_);
    crate::leanh::lean_dec(v___y_2458_);
    crate::leanh::lean_dec_ref(v___y_2457_);
    return v_res_2462_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2464_ = l_Lean_Level_ofNat(v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(
    mut v_ctor_u2081_2465_: *mut crate::leanh::LeanObject,
    mut v_args_u2081_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_b_2468_: *mut crate::leanh::LeanObject,
    mut v_x_2469_: *mut crate::leanh::LeanObject,
    mut v_x_2470_: *mut crate::leanh::LeanObject,
    mut v_x_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v_declName_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v_val_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v_val_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v_val_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v_val_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut v_a_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut v_a_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2659_: u8 = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut v_a_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut v_a_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2680_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_a_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_start_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_a_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2469_) == 5 {
                    v_fn_2483_ = crate::leanh::lean_ctor_get(v_x_2469_, 0);
                    crate::leanh::lean_inc_ref(v_fn_2483_);
                    v_arg_2484_ = crate::leanh::lean_ctor_get(v_x_2469_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2484_);
                    crate::leanh::lean_dec_ref_known(v_x_2469_, 2);
                    v___x_2485_ = lean_array_set(v_x_2470_, v_x_2471_, v_arg_2484_);
                    v___x_2486_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2487_ = lean_nat_sub(v_x_2471_, v___x_2486_);
                    crate::leanh::lean_dec(v_x_2471_);
                    v_x_2469_ = v_fn_2483_;
                    v_x_2470_ = v___x_2485_;
                    v_x_2471_ = v___x_2487_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2471_);
                    if crate::leanh::lean_obj_tag(v_ctor_u2081_2465_) == 4 {
                        v_declName_2489_ = crate::leanh::lean_ctor_get(v_ctor_u2081_2465_, 0);
                        crate::leanh::lean_inc(v_declName_2489_);
                        v_us_2490_ = crate::leanh::lean_ctor_get(v_ctor_u2081_2465_, 1);
                        crate::leanh::lean_inc(v_us_2490_);
                        crate::leanh::lean_dec_ref_known(v_ctor_u2081_2465_, 2);
                        if crate::leanh::lean_obj_tag(v_x_2469_) == 4 {
                            v_declName_2521_ = crate::leanh::lean_ctor_get(v_x_2469_, 0);
                            crate::leanh::lean_inc(v_declName_2521_);
                            v_us_2522_ = crate::leanh::lean_ctor_get(v_x_2469_, 1);
                            crate::leanh::lean_inc(v_us_2522_);
                            crate::leanh::lean_dec_ref_known(v_x_2469_, 2);
                            crate::leanh::lean_inc(v_declName_2489_);
                            v___x_2523_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_declName_2489_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
                            if crate::leanh::lean_obj_tag(v___x_2523_) == 0 {
                                v_a_2524_ = crate::leanh::lean_ctor_get(v___x_2523_, 0);
                                v_isSharedCheck_2720_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2523_)) as u8;
                                if v_isSharedCheck_2720_ == 0 {
                                    v___x_2526_ = v___x_2523_;
                                    v_isShared_2527_ = v_isSharedCheck_2720_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2524_);
                                    crate::leanh::lean_dec(v___x_2523_);
                                    v___x_2526_ = crate::leanh::lean_box(0);
                                    v_isShared_2527_ = v_isSharedCheck_2720_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_us_2522_);
                                crate::leanh::lean_dec(v_declName_2521_);
                                crate::leanh::lean_dec(v_us_2490_);
                                crate::leanh::lean_dec(v_declName_2489_);
                                crate::leanh::lean_dec_ref(v_x_2470_);
                                crate::leanh::lean_dec_ref(v_b_2468_);
                                crate::leanh::lean_dec_ref(v_a_2467_);
                                crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                                v_a_2721_ = crate::leanh::lean_ctor_get(v___x_2523_, 0);
                                v_isSharedCheck_2728_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2523_)) as u8;
                                if v_isSharedCheck_2728_ == 0 {
                                    v___x_2723_ = v___x_2523_;
                                    v_isShared_2724_ = v_isSharedCheck_2728_;
                                    state = 39;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2721_);
                                    crate::leanh::lean_dec(v___x_2523_);
                                    v___x_2723_ = crate::leanh::lean_box(0);
                                    v_isShared_2724_ = v_isSharedCheck_2728_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_us_2490_);
                            crate::leanh::lean_dec(v_declName_2489_);
                            crate::leanh::lean_dec_ref(v_x_2470_);
                            crate::leanh::lean_dec_ref(v_x_2469_);
                            crate::leanh::lean_dec_ref(v_b_2468_);
                            crate::leanh::lean_dec_ref(v_a_2467_);
                            crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                            v___x_2729_ = crate::leanh::lean_box(0);
                            v___x_2730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2729_);
                            return v___x_2730_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_2470_);
                        crate::leanh::lean_dec_ref(v_x_2469_);
                        crate::leanh::lean_dec_ref(v_b_2468_);
                        crate::leanh::lean_dec_ref(v_a_2467_);
                        crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                        crate::leanh::lean_dec_ref(v_ctor_u2081_2465_);
                        v___x_2731_ = crate::leanh::lean_box(0);
                        v___x_2732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2732_, 0, v___x_2731_);
                        return v___x_2732_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2493_);
                v___x_2504_ = l_Lean_mkConst(v___y_2493_, v_us_2490_);
                v___x_2505_ = l_Lean_mkAppN(v___x_2504_, v_args_u2081_2466_);
                crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                v___x_2506_ = l_Lean_mkAppN(v___x_2505_, v_x_2470_);
                crate::leanh::lean_dec_ref(v_x_2470_);
                crate::leanh::lean_inc(v___y_2503_);
                crate::leanh::lean_inc_ref(v___y_2502_);
                crate::leanh::lean_inc(v___y_2501_);
                crate::leanh::lean_inc_ref(v___y_2500_);
                crate::leanh::lean_inc_ref(v___x_2506_);
                v___x_2507_ = lean_infer_type(
                    v___x_2506_,
                    v___y_2500_,
                    v___y_2501_,
                    v___y_2502_,
                    v___y_2503_,
                );
                if crate::leanh::lean_obj_tag(v___x_2507_) == 0 {
                    v_a_2508_ = crate::leanh::lean_ctor_get(v___x_2507_, 0);
                    crate::leanh::lean_inc(v_a_2508_);
                    crate::leanh::lean_dec_ref_known(v___x_2507_, 1);
                    v___x_2509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2509_, 0, v___y_2493_);
                    v___x_2510_ = crate::leanh::lean_alloc_ctor(7, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2509_);
                    v___x_2511_ = crate::leanh::lean_box(1);
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
                    crate::leanh::lean_dec_ref(v___x_2506_);
                    crate::leanh::lean_dec(v___y_2493_);
                    crate::leanh::lean_dec(v___y_2492_);
                    v_a_2513_ = crate::leanh::lean_ctor_get(v___x_2507_, 0);
                    v_isSharedCheck_2520_ = (!crate::leanh::lean_is_exclusive(v___x_2507_)) as u8;
                    if v_isSharedCheck_2520_ == 0 {
                        v___x_2515_ = v___x_2507_;
                        v_isShared_2516_ = v_isSharedCheck_2520_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2513_);
                        crate::leanh::lean_dec(v___x_2507_);
                        v___x_2515_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
                    v___x_2518_ = v_reuseFailAlloc_2519_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2518_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2524_) == 6 {
                    v_val_2528_ = crate::leanh::lean_ctor_get(v_a_2524_, 0);
                    crate::leanh::lean_inc_ref(v_val_2528_);
                    crate::leanh::lean_dec_ref_known(v_a_2524_, 1);
                    crate::leanh::lean_inc(v_declName_2521_);
                    v___x_2529_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo_spec__0(v_declName_2521_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
                    if crate::leanh::lean_obj_tag(v___x_2529_) == 0 {
                        v_a_2530_ = crate::leanh::lean_ctor_get(v___x_2529_, 0);
                        v_isSharedCheck_2707_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2529_)) as u8;
                        if v_isSharedCheck_2707_ == 0 {
                            v___x_2532_ = v___x_2529_;
                            v_isShared_2533_ = v_isSharedCheck_2707_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2530_);
                            crate::leanh::lean_dec(v___x_2529_);
                            v___x_2532_ = crate::leanh::lean_box(0);
                            v_isShared_2533_ = v_isSharedCheck_2707_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_val_2528_);
                        crate::leanh::lean_del_object(v___x_2526_);
                        crate::leanh::lean_dec(v_us_2522_);
                        crate::leanh::lean_dec(v_declName_2521_);
                        crate::leanh::lean_dec(v_us_2490_);
                        crate::leanh::lean_dec(v_declName_2489_);
                        crate::leanh::lean_dec_ref(v_x_2470_);
                        crate::leanh::lean_dec_ref(v_b_2468_);
                        crate::leanh::lean_dec_ref(v_a_2467_);
                        crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                        v_a_2708_ = crate::leanh::lean_ctor_get(v___x_2529_, 0);
                        v_isSharedCheck_2715_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2529_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2710_ = v___x_2529_;
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2708_);
                            crate::leanh::lean_dec(v___x_2529_);
                            v___x_2710_ = crate::leanh::lean_box(0);
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 36;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2524_);
                    crate::leanh::lean_dec(v_us_2522_);
                    crate::leanh::lean_dec(v_declName_2521_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec(v_declName_2489_);
                    crate::leanh::lean_dec_ref(v_x_2470_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2716_ = crate::leanh::lean_box(0);
                    if v_isShared_2527_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2716_);
                        v___x_2718_ = v___x_2526_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2719_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                        v___x_2718_ = v_reuseFailAlloc_2719_;
                        state = 38;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_2530_) == 6 {
                    v_val_2534_ = crate::leanh::lean_ctor_get(v_a_2530_, 0);
                    crate::leanh::lean_inc_ref(v_val_2534_);
                    crate::leanh::lean_dec_ref_known(v_a_2530_, 1);
                    v_induct_2535_ = crate::leanh::lean_ctor_get(v_val_2528_, 1);
                    crate::leanh::lean_inc(v_induct_2535_);
                    v_numParams_2536_ = crate::leanh::lean_ctor_get(v_val_2528_, 3);
                    crate::leanh::lean_inc(v_numParams_2536_);
                    crate::leanh::lean_dec_ref(v_val_2528_);
                    v_induct_2537_ = crate::leanh::lean_ctor_get(v_val_2534_, 1);
                    crate::leanh::lean_inc(v_induct_2537_);
                    v_numParams_2538_ = crate::leanh::lean_ctor_get(v_val_2534_, 3);
                    crate::leanh::lean_inc(v_numParams_2538_);
                    crate::leanh::lean_dec_ref(v_val_2534_);
                    v___x_2539_ = lean_name_eq(v_induct_2535_, v_induct_2537_);
                    crate::leanh::lean_dec(v_induct_2537_);
                    if v___x_2539_ == 0 {
                        crate::leanh::lean_dec(v_numParams_2538_);
                        crate::leanh::lean_dec(v_numParams_2536_);
                        crate::leanh::lean_dec(v_induct_2535_);
                        crate::leanh::lean_del_object(v___x_2526_);
                        crate::leanh::lean_dec(v_us_2522_);
                        crate::leanh::lean_dec(v_declName_2521_);
                        crate::leanh::lean_dec(v_us_2490_);
                        crate::leanh::lean_dec(v_declName_2489_);
                        crate::leanh::lean_dec_ref(v_x_2470_);
                        crate::leanh::lean_dec_ref(v_b_2468_);
                        crate::leanh::lean_dec_ref(v_a_2467_);
                        crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                        v___x_2540_ = crate::leanh::lean_box(0);
                        if v_isShared_2533_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2540_);
                            v___x_2542_ = v___x_2532_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2543_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
                            v___x_2542_ = v_reuseFailAlloc_2543_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_2544_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_args_u2081_2466_);
                        v___x_2545_ = l_Array_toSubarray___redArg(
                            v_args_u2081_2466_,
                            v___x_2544_,
                            v_numParams_2536_,
                        );
                        v_start_2546_ = crate::leanh::lean_ctor_get(v___x_2545_, 1);
                        crate::leanh::lean_inc(v_start_2546_);
                        v_stop_2547_ = crate::leanh::lean_ctor_get(v___x_2545_, 2);
                        crate::leanh::lean_inc(v_stop_2547_);
                        crate::leanh::lean_inc_ref(v_x_2470_);
                        v___x_2548_ =
                            l_Array_toSubarray___redArg(v_x_2470_, v___x_2544_, v_numParams_2538_);
                        v_start_2694_ = crate::leanh::lean_ctor_get(v___x_2548_, 1);
                        crate::leanh::lean_inc(v_start_2694_);
                        v_stop_2695_ = crate::leanh::lean_ctor_get(v___x_2548_, 2);
                        crate::leanh::lean_inc(v_stop_2695_);
                        v___x_2696_ = lean_nat_sub(v_stop_2547_, v_start_2546_);
                        crate::leanh::lean_dec(v_start_2546_);
                        crate::leanh::lean_dec(v_stop_2547_);
                        v___x_2697_ = lean_nat_sub(v_stop_2695_, v_start_2694_);
                        crate::leanh::lean_dec(v_start_2694_);
                        crate::leanh::lean_dec(v_stop_2695_);
                        v___x_2698_ = lean_nat_dec_eq(v___x_2696_, v___x_2697_);
                        crate::leanh::lean_dec(v___x_2697_);
                        crate::leanh::lean_dec(v___x_2696_);
                        if v___x_2698_ == 0 {
                            if v___x_2539_ == 0 {
                                crate::leanh::lean_del_object(v___x_2526_);
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2548_);
                                crate::leanh::lean_dec_ref(v___x_2545_);
                                crate::leanh::lean_dec(v_induct_2535_);
                                crate::leanh::lean_del_object(v___x_2532_);
                                crate::leanh::lean_dec(v_us_2522_);
                                crate::leanh::lean_dec(v_declName_2521_);
                                crate::leanh::lean_dec(v_us_2490_);
                                crate::leanh::lean_dec(v_declName_2489_);
                                crate::leanh::lean_dec_ref(v_x_2470_);
                                crate::leanh::lean_dec_ref(v_b_2468_);
                                crate::leanh::lean_dec_ref(v_a_2467_);
                                crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                                v___x_2699_ = crate::leanh::lean_box(0);
                                if v_isShared_2527_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2699_);
                                    v___x_2701_ = v___x_2526_;
                                    state = 34;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2702_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
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
                            crate::leanh::lean_del_object(v___x_2526_);
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2530_);
                    crate::leanh::lean_dec_ref(v_val_2528_);
                    crate::leanh::lean_del_object(v___x_2526_);
                    crate::leanh::lean_dec(v_us_2522_);
                    crate::leanh::lean_dec(v_declName_2521_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec(v_declName_2489_);
                    crate::leanh::lean_dec_ref(v_x_2470_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2703_ = crate::leanh::lean_box(0);
                    if v_isShared_2533_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2703_);
                        v___x_2705_ = v___x_2532_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_2706_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
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
                crate::leanh::lean_dec(v_declName_2521_);
                if v___x_2551_ == 0 {
                    crate::leanh::lean_dec(v_declName_2489_);
                    crate::leanh::lean_dec_ref(v_x_2470_);
                    crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                    crate::leanh::lean_inc_ref(v_a_2467_);
                    v___x_2552_ = l_Lean_Meta_getCtorAppIndices_x3f(
                        v_a_2467_,
                        v___y_2478_,
                        v___y_2479_,
                        v___y_2480_,
                        v___y_2481_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2552_) == 0 {
                        v_a_2553_ = crate::leanh::lean_ctor_get(v___x_2552_, 0);
                        v_isSharedCheck_2631_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2552_)) as u8;
                        if v_isSharedCheck_2631_ == 0 {
                            v___x_2555_ = v___x_2552_;
                            v_isShared_2556_ = v_isSharedCheck_2631_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2553_);
                            crate::leanh::lean_dec(v___x_2552_);
                            v___x_2555_ = crate::leanh::lean_box(0);
                            v_isShared_2556_ = v_isSharedCheck_2631_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2550_);
                        crate::leanh::lean_dec_ref(v___x_2548_);
                        crate::leanh::lean_dec_ref(v___x_2545_);
                        crate::leanh::lean_dec(v_induct_2535_);
                        crate::leanh::lean_dec(v_us_2490_);
                        crate::leanh::lean_dec_ref(v_b_2468_);
                        crate::leanh::lean_dec_ref(v_a_2467_);
                        v_a_2632_ = crate::leanh::lean_ctor_get(v___x_2552_, 0);
                        v_isSharedCheck_2639_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2552_)) as u8;
                        if v_isSharedCheck_2639_ == 0 {
                            v___x_2634_ = v___x_2552_;
                            v_isShared_2635_ = v_isSharedCheck_2639_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2632_);
                            crate::leanh::lean_dec(v___x_2552_);
                            v___x_2634_ = crate::leanh::lean_box(0);
                            v_isShared_2635_ = v_isSharedCheck_2639_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    v___x_2640_ = lean_st_ref_get(v___y_2481_);
                    v_env_2641_ = crate::leanh::lean_ctor_get(v___x_2640_, 0);
                    crate::leanh::lean_inc_ref(v_env_2641_);
                    crate::leanh::lean_dec(v___x_2640_);
                    v___x_2642_ = l_Lean_Meta_mkHInjectiveTheoremNameFor(v_declName_2489_);
                    v___x_2643_ = l_Lean_Environment_containsOnBranch(v_env_2641_, v___x_2642_);
                    crate::leanh::lean_dec_ref(v_env_2641_);
                    if v___x_2643_ == 0 {
                        crate::leanh::lean_inc(v___x_2642_);
                        v___x_2644_ =
                            l_Lean_executeReservedNameAction(v___x_2642_, v___y_2480_, v___y_2481_);
                        if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2644_, 1);
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
                            crate::leanh::lean_dec(v___x_2642_);
                            crate::leanh::lean_dec(v___y_2550_);
                            crate::leanh::lean_dec(v_us_2490_);
                            crate::leanh::lean_dec_ref(v_x_2470_);
                            crate::leanh::lean_dec_ref(v_args_u2081_2466_);
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
                if crate::leanh::lean_obj_tag(v_a_2553_) == 1 {
                    crate::leanh::lean_del_object(v___x_2555_);
                    v_val_2557_ = crate::leanh::lean_ctor_get(v_a_2553_, 0);
                    v_isSharedCheck_2626_ = (!crate::leanh::lean_is_exclusive(v_a_2553_)) as u8;
                    if v_isSharedCheck_2626_ == 0 {
                        v___x_2559_ = v_a_2553_;
                        v_isShared_2560_ = v_isSharedCheck_2626_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2557_);
                        crate::leanh::lean_dec(v_a_2553_);
                        v___x_2559_ = crate::leanh::lean_box(0);
                        v_isShared_2560_ = v_isSharedCheck_2626_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2553_);
                    crate::leanh::lean_dec(v___y_2550_);
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    v___x_2627_ = crate::leanh::lean_box(0);
                    if v_isShared_2556_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2627_);
                        v___x_2629_ = v___x_2555_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
                        v___x_2629_ = v_reuseFailAlloc_2630_;
                        state = 21;
                        continue;
                    }
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v_b_2468_);
                v___x_2561_ = l_Lean_Meta_getCtorAppIndices_x3f(
                    v_b_2468_,
                    v___y_2478_,
                    v___y_2479_,
                    v___y_2480_,
                    v___y_2481_,
                );
                if crate::leanh::lean_obj_tag(v___x_2561_) == 0 {
                    v_a_2562_ = crate::leanh::lean_ctor_get(v___x_2561_, 0);
                    v_isSharedCheck_2617_ = (!crate::leanh::lean_is_exclusive(v___x_2561_)) as u8;
                    if v_isSharedCheck_2617_ == 0 {
                        v___x_2564_ = v___x_2561_;
                        v_isShared_2565_ = v_isSharedCheck_2617_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2562_);
                        crate::leanh::lean_dec(v___x_2561_);
                        v___x_2564_ = crate::leanh::lean_box(0);
                        v_isShared_2565_ = v_isSharedCheck_2617_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2559_);
                    crate::leanh::lean_dec(v_val_2557_);
                    crate::leanh::lean_dec(v___y_2550_);
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    v_a_2618_ = crate::leanh::lean_ctor_get(v___x_2561_, 0);
                    v_isSharedCheck_2625_ = (!crate::leanh::lean_is_exclusive(v___x_2561_)) as u8;
                    if v_isSharedCheck_2625_ == 0 {
                        v___x_2620_ = v___x_2561_;
                        v_isShared_2621_ = v_isSharedCheck_2625_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2618_);
                        crate::leanh::lean_dec(v___x_2561_);
                        v___x_2620_ = crate::leanh::lean_box(0);
                        v_isShared_2621_ = v_isSharedCheck_2625_;
                        state = 19;
                        continue;
                    }
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_2562_) == 1 {
                    crate::leanh::lean_del_object(v___x_2564_);
                    v_val_2566_ = crate::leanh::lean_ctor_get(v_a_2562_, 0);
                    v_isSharedCheck_2612_ = (!crate::leanh::lean_is_exclusive(v_a_2562_)) as u8;
                    if v_isSharedCheck_2612_ == 0 {
                        v___x_2568_ = v_a_2562_;
                        v_isShared_2569_ = v_isSharedCheck_2612_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2566_);
                        crate::leanh::lean_dec(v_a_2562_);
                        v___x_2568_ = crate::leanh::lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2612_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2562_);
                    crate::leanh::lean_del_object(v___x_2559_);
                    crate::leanh::lean_dec(v_val_2557_);
                    crate::leanh::lean_dec(v___y_2550_);
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    v___x_2613_ = crate::leanh::lean_box(0);
                    if v_isShared_2565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2613_);
                        v___x_2615_ = v___x_2564_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
                        v___x_2615_ = v_reuseFailAlloc_2616_;
                        state = 18;
                        continue;
                    }
                }
            }
            11 => {
                v___x_2570_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_2476_);
                if crate::leanh::lean_obj_tag(v___x_2570_) == 0 {
                    v_a_2571_ = crate::leanh::lean_ctor_get(v___x_2570_, 0);
                    crate::leanh::lean_inc(v_a_2571_);
                    crate::leanh::lean_dec_ref_known(v___x_2570_, 1);
                    v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo___closed__0;
                    v___x_2573_ = l_Lean_Name_str___override(v_induct_2535_, v___x_2572_);
                    v___x_2574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1___closed__0);
                    v___x_2575_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2574_);
                    crate::leanh::lean_ctor_set(v___x_2575_, 1, v_us_2490_);
                    crate::leanh::lean_inc(v___x_2573_);
                    v___x_2576_ = l_Lean_mkConst(v___x_2573_, v___x_2575_);
                    v___x_2577_ = l_Lean_Expr_app___override(v___x_2576_, v_a_2571_);
                    v___x_2578_ = l_Subarray_copy___redArg(v___x_2545_);
                    v___x_2579_ = l_Array_append___redArg(v___x_2578_, v_val_2557_);
                    crate::leanh::lean_dec(v_val_2557_);
                    v___x_2580_ = l_Lean_mkAppN(v___x_2577_, v___x_2579_);
                    crate::leanh::lean_dec_ref(v___x_2579_);
                    v___x_2581_ = l_Lean_Expr_app___override(v___x_2580_, v_a_2467_);
                    v___x_2582_ = l_Subarray_copy___redArg(v___x_2548_);
                    v___x_2583_ = l_Array_append___redArg(v___x_2582_, v_val_2566_);
                    crate::leanh::lean_dec(v_val_2566_);
                    v___x_2584_ = l_Lean_mkAppN(v___x_2581_, v___x_2583_);
                    crate::leanh::lean_dec_ref(v___x_2583_);
                    v___x_2585_ = l_Lean_Expr_app___override(v___x_2584_, v_b_2468_);
                    crate::leanh::lean_inc(v___y_2481_);
                    crate::leanh::lean_inc_ref(v___y_2480_);
                    crate::leanh::lean_inc(v___y_2479_);
                    crate::leanh::lean_inc_ref(v___y_2478_);
                    crate::leanh::lean_inc_ref(v___x_2585_);
                    v___x_2586_ = lean_infer_type(
                        v___x_2585_,
                        v___y_2478_,
                        v___y_2479_,
                        v___y_2480_,
                        v___y_2481_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2586_) == 0 {
                        v_a_2587_ = crate::leanh::lean_ctor_get(v___x_2586_, 0);
                        crate::leanh::lean_inc(v_a_2587_);
                        crate::leanh::lean_dec_ref_known(v___x_2586_, 1);
                        if v_isShared_2569_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2568_, 0);
                            crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2573_);
                            v___x_2589_ = v___x_2568_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2595_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2573_);
                            v___x_2589_ = v_reuseFailAlloc_2595_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2585_);
                        crate::leanh::lean_dec(v___x_2573_);
                        crate::leanh::lean_del_object(v___x_2568_);
                        crate::leanh::lean_del_object(v___x_2559_);
                        crate::leanh::lean_dec(v___y_2550_);
                        v_a_2596_ = crate::leanh::lean_ctor_get(v___x_2586_, 0);
                        v_isSharedCheck_2603_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2586_)) as u8;
                        if v_isSharedCheck_2603_ == 0 {
                            v___x_2598_ = v___x_2586_;
                            v_isShared_2599_ = v_isSharedCheck_2603_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2596_);
                            crate::leanh::lean_dec(v___x_2586_);
                            v___x_2598_ = crate::leanh::lean_box(0);
                            v_isShared_2599_ = v_isSharedCheck_2603_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2568_);
                    crate::leanh::lean_dec(v_val_2566_);
                    crate::leanh::lean_del_object(v___x_2559_);
                    crate::leanh::lean_dec(v_val_2557_);
                    crate::leanh::lean_dec(v___y_2550_);
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    v_a_2604_ = crate::leanh::lean_ctor_get(v___x_2570_, 0);
                    v_isSharedCheck_2611_ = (!crate::leanh::lean_is_exclusive(v___x_2570_)) as u8;
                    if v_isSharedCheck_2611_ == 0 {
                        v___x_2606_ = v___x_2570_;
                        v_isShared_2607_ = v_isSharedCheck_2611_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2604_);
                        crate::leanh::lean_dec(v___x_2570_);
                        v___x_2606_ = crate::leanh::lean_box(0);
                        v_isShared_2607_ = v_isSharedCheck_2611_;
                        state = 16;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2560_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2559_, 7);
                    crate::leanh::lean_ctor_set(v___x_2559_, 0, v___x_2589_);
                    v___x_2591_ = v___x_2559_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2594_ = crate::leanh::lean_alloc_ctor(7, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2589_);
                    v___x_2591_ = v_reuseFailAlloc_2594_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2592_ = crate::leanh::lean_box(1);
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
                    v_reuseFailAlloc_2602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
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
                    v_reuseFailAlloc_2610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
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
                    v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
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
                    v_reuseFailAlloc_2638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
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
                crate::leanh::lean_dec(v___x_2647_);
                crate::leanh::lean_dec(v___x_2646_);
                if v___x_2648_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec(v_us_2522_);
                    crate::leanh::lean_dec(v_declName_2521_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec(v_declName_2489_);
                    crate::leanh::lean_dec_ref(v_x_2470_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2649_ = crate::leanh::lean_box(0);
                    if v_isShared_2533_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2649_);
                        v___x_2651_ = v___x_2532_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
                        v___x_2651_ = v_reuseFailAlloc_2652_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2532_);
                    crate::leanh::lean_inc(v_us_2490_);
                    v___x_2653_ = l_List_zipWith___at___00List_zip_spec__0(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_us_2490_,
                        v_us_2522_,
                    );
                    v___x_2654_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(v___x_2653_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
                    if crate::leanh::lean_obj_tag(v___x_2654_) == 0 {
                        v_a_2655_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
                        v_isSharedCheck_2685_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2654_)) as u8;
                        if v_isSharedCheck_2685_ == 0 {
                            v___x_2657_ = v___x_2654_;
                            v_isShared_2658_ = v_isSharedCheck_2685_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2655_);
                            crate::leanh::lean_dec(v___x_2654_);
                            v___x_2657_ = crate::leanh::lean_box(0);
                            v_isShared_2658_ = v_isSharedCheck_2685_;
                            state = 26;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2548_);
                        crate::leanh::lean_dec_ref(v___x_2545_);
                        crate::leanh::lean_dec(v_induct_2535_);
                        crate::leanh::lean_dec(v_declName_2521_);
                        crate::leanh::lean_dec(v_us_2490_);
                        crate::leanh::lean_dec(v_declName_2489_);
                        crate::leanh::lean_dec_ref(v_x_2470_);
                        crate::leanh::lean_dec_ref(v_b_2468_);
                        crate::leanh::lean_dec_ref(v_a_2467_);
                        crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                        v_a_2686_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
                        v_isSharedCheck_2693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2654_)) as u8;
                        if v_isSharedCheck_2693_ == 0 {
                            v___x_2688_ = v___x_2654_;
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2686_);
                            crate::leanh::lean_dec(v___x_2654_);
                            v___x_2688_ = crate::leanh::lean_box(0);
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
                v___x_2659_ = (crate::leanh::lean_unbox(v_a_2655_) as u8);
                crate::leanh::lean_dec(v_a_2655_);
                if v___x_2659_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2548_);
                    crate::leanh::lean_dec_ref(v___x_2545_);
                    crate::leanh::lean_dec(v_induct_2535_);
                    crate::leanh::lean_dec(v_declName_2521_);
                    crate::leanh::lean_dec(v_us_2490_);
                    crate::leanh::lean_dec(v_declName_2489_);
                    crate::leanh::lean_dec_ref(v_x_2470_);
                    crate::leanh::lean_dec_ref(v_b_2468_);
                    crate::leanh::lean_dec_ref(v_a_2467_);
                    crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                    v___x_2660_ = crate::leanh::lean_box(0);
                    if v_isShared_2658_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2660_);
                        v___x_2662_ = v___x_2657_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
                        v___x_2662_ = v_reuseFailAlloc_2663_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2657_);
                    v___x_2664_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2467_, v___y_2472_);
                    if crate::leanh::lean_obj_tag(v___x_2664_) == 0 {
                        v_a_2665_ = crate::leanh::lean_ctor_get(v___x_2664_, 0);
                        crate::leanh::lean_inc(v_a_2665_);
                        crate::leanh::lean_dec_ref_known(v___x_2664_, 1);
                        v___x_2666_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_b_2468_, v___y_2472_);
                        if crate::leanh::lean_obj_tag(v___x_2666_) == 0 {
                            v_a_2667_ = crate::leanh::lean_ctor_get(v___x_2666_, 0);
                            crate::leanh::lean_inc(v_a_2667_);
                            crate::leanh::lean_dec_ref_known(v___x_2666_, 1);
                            v___x_2668_ = lean_nat_dec_le(v_a_2665_, v_a_2667_);
                            if v___x_2668_ == 0 {
                                crate::leanh::lean_dec(v_a_2667_);
                                v___y_2550_ = v_a_2665_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_2665_);
                                v___y_2550_ = v_a_2667_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2665_);
                            crate::leanh::lean_dec_ref(v___x_2548_);
                            crate::leanh::lean_dec_ref(v___x_2545_);
                            crate::leanh::lean_dec(v_induct_2535_);
                            crate::leanh::lean_dec(v_declName_2521_);
                            crate::leanh::lean_dec(v_us_2490_);
                            crate::leanh::lean_dec(v_declName_2489_);
                            crate::leanh::lean_dec_ref(v_x_2470_);
                            crate::leanh::lean_dec_ref(v_b_2468_);
                            crate::leanh::lean_dec_ref(v_a_2467_);
                            crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                            v_a_2669_ = crate::leanh::lean_ctor_get(v___x_2666_, 0);
                            v_isSharedCheck_2676_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2666_)) as u8;
                            if v_isSharedCheck_2676_ == 0 {
                                v___x_2671_ = v___x_2666_;
                                v_isShared_2672_ = v_isSharedCheck_2676_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2669_);
                                crate::leanh::lean_dec(v___x_2666_);
                                v___x_2671_ = crate::leanh::lean_box(0);
                                v_isShared_2672_ = v_isSharedCheck_2676_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2548_);
                        crate::leanh::lean_dec_ref(v___x_2545_);
                        crate::leanh::lean_dec(v_induct_2535_);
                        crate::leanh::lean_dec(v_declName_2521_);
                        crate::leanh::lean_dec(v_us_2490_);
                        crate::leanh::lean_dec(v_declName_2489_);
                        crate::leanh::lean_dec_ref(v_x_2470_);
                        crate::leanh::lean_dec_ref(v_b_2468_);
                        crate::leanh::lean_dec_ref(v_a_2467_);
                        crate::leanh::lean_dec_ref(v_args_u2081_2466_);
                        v_a_2677_ = crate::leanh::lean_ctor_get(v___x_2664_, 0);
                        v_isSharedCheck_2684_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2664_)) as u8;
                        if v_isSharedCheck_2684_ == 0 {
                            v___x_2679_ = v___x_2664_;
                            v_isShared_2680_ = v_isSharedCheck_2684_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2677_);
                            crate::leanh::lean_dec(v___x_2664_);
                            v___x_2679_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
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
                    v_reuseFailAlloc_2683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
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
                    v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
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
                    v_reuseFailAlloc_2714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
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
                    v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctor_u2081_2733_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_args_u2081_2734_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_2735_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_b_2736_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_x_2737_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_x_2738_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_x_2739_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2740_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2741_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2742_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2743_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2744_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2745_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2746_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2747_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2748_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2749_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2750_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(v_ctor_u2081_2733_, v_args_u2081_2734_, v_a_2735_, v_b_2736_, v_x_2737_, v_x_2738_, v_x_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
    crate::leanh::lean_dec(v___y_2749_);
    crate::leanh::lean_dec_ref(v___y_2748_);
    crate::leanh::lean_dec(v___y_2747_);
    crate::leanh::lean_dec_ref(v___y_2746_);
    crate::leanh::lean_dec(v___y_2745_);
    crate::leanh::lean_dec_ref(v___y_2744_);
    crate::leanh::lean_dec(v___y_2743_);
    crate::leanh::lean_dec_ref(v___y_2742_);
    crate::leanh::lean_dec(v___y_2741_);
    crate::leanh::lean_dec(v___y_2740_);
    return v_res_2751_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = crate::leanh::lean_box(0);
    v_dummy_2753_ = l_Lean_Expr_sort___override(v___x_2752_);
    return v_dummy_2753_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2(
    mut v_b_2754_: *mut crate::leanh::LeanObject,
    mut v_a_2755_: *mut crate::leanh::LeanObject,
    mut v_x_2756_: *mut crate::leanh::LeanObject,
    mut v_x_2757_: *mut crate::leanh::LeanObject,
    mut v_x_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
    mut v___y_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2756_) == 5 {
                    v_fn_2770_ = crate::leanh::lean_ctor_get(v_x_2756_, 0);
                    crate::leanh::lean_inc_ref(v_fn_2770_);
                    v_arg_2771_ = crate::leanh::lean_ctor_get(v_x_2756_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2771_);
                    crate::leanh::lean_dec_ref_known(v_x_2756_, 2);
                    v___x_2772_ = lean_array_set(v_x_2757_, v_x_2758_, v_arg_2771_);
                    v___x_2773_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2774_ = lean_nat_sub(v_x_2758_, v___x_2773_);
                    crate::leanh::lean_dec(v_x_2758_);
                    v_x_2756_ = v_fn_2770_;
                    v_x_2757_ = v___x_2772_;
                    v_x_2758_ = v___x_2774_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2758_);
                    v_dummy_2776_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0);
                    v_nargs_2777_ = l_Lean_Expr_getAppNumArgs(v_b_2754_);
                    crate::leanh::lean_inc(v_nargs_2777_);
                    v___x_2778_ = lean_mk_array(v_nargs_2777_, v_dummy_2776_);
                    v___x_2779_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2780_ = lean_nat_sub(v_nargs_2777_, v___x_2779_);
                    crate::leanh::lean_dec(v_nargs_2777_);
                    crate::leanh::lean_inc_ref(v_b_2754_);
                    v___x_2781_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(v_x_2756_, v_x_2757_, v_a_2755_, v_b_2754_, v_b_2754_, v___x_2778_, v___x_2780_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
                    return v___x_2781_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___boxed(
    mut v_b_2782_: *mut crate::leanh::LeanObject,
    mut v_a_2783_: *mut crate::leanh::LeanObject,
    mut v_x_2784_: *mut crate::leanh::LeanObject,
    mut v_x_2785_: *mut crate::leanh::LeanObject,
    mut v_x_2786_: *mut crate::leanh::LeanObject,
    mut v___y_2787_: *mut crate::leanh::LeanObject,
    mut v___y_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
    mut v___y_2790_: *mut crate::leanh::LeanObject,
    mut v___y_2791_: *mut crate::leanh::LeanObject,
    mut v___y_2792_: *mut crate::leanh::LeanObject,
    mut v___y_2793_: *mut crate::leanh::LeanObject,
    mut v___y_2794_: *mut crate::leanh::LeanObject,
    mut v___y_2795_: *mut crate::leanh::LeanObject,
    mut v___y_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2(v_b_2782_, v_a_2783_, v_x_2784_, v_x_2785_, v_x_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
    crate::leanh::lean_dec(v___y_2796_);
    crate::leanh::lean_dec_ref(v___y_2795_);
    crate::leanh::lean_dec(v___y_2794_);
    crate::leanh::lean_dec_ref(v___y_2793_);
    crate::leanh::lean_dec(v___y_2792_);
    crate::leanh::lean_dec_ref(v___y_2791_);
    crate::leanh::lean_dec(v___y_2790_);
    crate::leanh::lean_dec_ref(v___y_2789_);
    crate::leanh::lean_dec(v___y_2788_);
    crate::leanh::lean_dec(v___y_2787_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2(
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_b_2800_: *mut crate::leanh::LeanObject,
    mut v_x_2801_: *mut crate::leanh::LeanObject,
    mut v_x_2802_: *mut crate::leanh::LeanObject,
    mut v_x_2803_: *mut crate::leanh::LeanObject,
    mut v___y_2804_: *mut crate::leanh::LeanObject,
    mut v___y_2805_: *mut crate::leanh::LeanObject,
    mut v___y_2806_: *mut crate::leanh::LeanObject,
    mut v___y_2807_: *mut crate::leanh::LeanObject,
    mut v___y_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
    mut v___y_2813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2801_) == 5 {
        let mut v_fn_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_arg_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fn_2815_ = crate::leanh::lean_ctor_get(v_x_2801_, 0);
        crate::leanh::lean_inc_ref(v_fn_2815_);
        v_arg_2816_ = crate::leanh::lean_ctor_get(v_x_2801_, 1);
        crate::leanh::lean_inc_ref(v_arg_2816_);
        crate::leanh::lean_dec_ref_known(v_x_2801_, 2);
        v___x_2817_ = lean_array_set(v_x_2802_, v_x_2803_, v_arg_2816_);
        v___x_2818_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2819_ = lean_nat_sub(v_x_2803_, v___x_2818_);
        v___x_2820_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2(v_b_2800_, v_a_2799_, v_fn_2815_, v___x_2817_, v___x_2819_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
        return v___x_2820_;
    } else {
        let mut v_dummy_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nargs_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_dummy_2821_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0);
        v_nargs_2822_ = l_Lean_Expr_getAppNumArgs(v_b_2800_);
        crate::leanh::lean_inc(v_nargs_2822_);
        v___x_2823_ = lean_mk_array(v_nargs_2822_, v_dummy_2821_);
        v___x_2824_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2825_ = lean_nat_sub(v_nargs_2822_, v___x_2824_);
        crate::leanh::lean_dec(v_nargs_2822_);
        crate::leanh::lean_inc_ref(v_b_2800_);
        v___x_2826_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__1(v_x_2801_, v_x_2802_, v_a_2799_, v_b_2800_, v_b_2800_, v___x_2823_, v___x_2825_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
        return v___x_2826_;
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2___boxed(
    mut v_a_2827_: *mut crate::leanh::LeanObject,
    mut v_b_2828_: *mut crate::leanh::LeanObject,
    mut v_x_2829_: *mut crate::leanh::LeanObject,
    mut v_x_2830_: *mut crate::leanh::LeanObject,
    mut v_x_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
    mut v___y_2841_: *mut crate::leanh::LeanObject,
    mut v___y_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2843_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2(v_a_2827_, v_b_2828_, v_x_2829_, v_x_2830_, v_x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
    crate::leanh::lean_dec(v___y_2841_);
    crate::leanh::lean_dec_ref(v___y_2840_);
    crate::leanh::lean_dec(v___y_2839_);
    crate::leanh::lean_dec_ref(v___y_2838_);
    crate::leanh::lean_dec(v___y_2837_);
    crate::leanh::lean_dec_ref(v___y_2836_);
    crate::leanh::lean_dec(v___y_2835_);
    crate::leanh::lean_dec_ref(v___y_2834_);
    crate::leanh::lean_dec(v___y_2833_);
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec(v_x_2831_);
    return v_res_2843_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero(
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_b_2845_: *mut crate::leanh::LeanObject,
    mut v_a_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
    mut v_a_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_2857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2_spec__2___closed__0);
    v_nargs_2858_ = l_Lean_Expr_getAppNumArgs(v_a_2844_);
    crate::leanh::lean_inc(v_nargs_2858_);
    v___x_2859_ = lean_mk_array(v_nargs_2858_, v_dummy_2857_);
    v___x_2860_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2861_ = lean_nat_sub(v_nargs_2858_, v___x_2860_);
    crate::leanh::lean_dec(v_nargs_2858_);
    crate::leanh::lean_inc_ref(v_a_2844_);
    v___x_2862_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__2(v_a_2844_, v_b_2845_, v_a_2844_, v___x_2859_, v___x_2861_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
    crate::leanh::lean_dec(v___x_2861_);
    return v___x_2862_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero___boxed(
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_b_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
    mut v_a_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2876_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero(
        v_a_2863_, v_b_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_,
        v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_,
    );
    crate::leanh::lean_dec(v_a_2874_);
    crate::leanh::lean_dec_ref(v_a_2873_);
    crate::leanh::lean_dec(v_a_2872_);
    crate::leanh::lean_dec_ref(v_a_2871_);
    crate::leanh::lean_dec(v_a_2870_);
    crate::leanh::lean_dec_ref(v_a_2869_);
    crate::leanh::lean_dec(v_a_2868_);
    crate::leanh::lean_dec_ref(v_a_2867_);
    crate::leanh::lean_dec(v_a_2866_);
    crate::leanh::lean_dec(v_a_2865_);
    return v_res_2876_;
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0(
    mut v_x_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___redArg(v_x_2877_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    return v___x_2889_;
}
pub unsafe fn l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0___boxed(
    mut v_x_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_List_allM___at___00__private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero_spec__0(v_x_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
    crate::leanh::lean_dec(v___y_2900_);
    crate::leanh::lean_dec_ref(v___y_2899_);
    crate::leanh::lean_dec(v___y_2898_);
    crate::leanh::lean_dec_ref(v___y_2897_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    crate::leanh::lean_dec(v___y_2894_);
    crate::leanh::lean_dec_ref(v___y_2893_);
    crate::leanh::lean_dec(v___y_2892_);
    crate::leanh::lean_dec(v___y_2891_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateCtor(
    mut v_a_2903_: *mut crate::leanh::LeanObject,
    mut v_b_2904_: *mut crate::leanh::LeanObject,
    mut v_a_2905_: *mut crate::leanh::LeanObject,
    mut v_a_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_a_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut v_a_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_a_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_a_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2914_);
                crate::leanh::lean_inc_ref(v_a_2913_);
                crate::leanh::lean_inc(v_a_2912_);
                crate::leanh::lean_inc_ref(v_a_2911_);
                crate::leanh::lean_inc_ref(v_a_2903_);
                v___x_2916_ =
                    lean_infer_type(v_a_2903_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                if crate::leanh::lean_obj_tag(v___x_2916_) == 0 {
                    v_a_2917_ = crate::leanh::lean_ctor_get(v___x_2916_, 0);
                    crate::leanh::lean_inc(v_a_2917_);
                    crate::leanh::lean_dec_ref_known(v___x_2916_, 1);
                    v___x_2918_ =
                        l_Lean_Meta_whnfD(v_a_2917_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                    if crate::leanh::lean_obj_tag(v___x_2918_) == 0 {
                        v_a_2919_ = crate::leanh::lean_ctor_get(v___x_2918_, 0);
                        crate::leanh::lean_inc(v_a_2919_);
                        crate::leanh::lean_dec_ref_known(v___x_2918_, 1);
                        crate::leanh::lean_inc(v_a_2914_);
                        crate::leanh::lean_inc_ref(v_a_2913_);
                        crate::leanh::lean_inc(v_a_2912_);
                        crate::leanh::lean_inc_ref(v_a_2911_);
                        crate::leanh::lean_inc_ref(v_b_2904_);
                        v___x_2920_ =
                            lean_infer_type(v_b_2904_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                        if crate::leanh::lean_obj_tag(v___x_2920_) == 0 {
                            v_a_2921_ = crate::leanh::lean_ctor_get(v___x_2920_, 0);
                            crate::leanh::lean_inc(v_a_2921_);
                            crate::leanh::lean_dec_ref_known(v___x_2920_, 1);
                            v___x_2922_ = l_Lean_Meta_whnfD(
                                v_a_2921_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2922_) == 0 {
                                v_a_2923_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                                crate::leanh::lean_inc(v_a_2923_);
                                crate::leanh::lean_dec_ref_known(v___x_2922_, 1);
                                crate::leanh::lean_inc(v_a_2919_);
                                v___x_2924_ = l_Lean_Meta_isDefEqD(
                                    v_a_2919_, v_a_2923_, v_a_2911_, v_a_2912_, v_a_2913_,
                                    v_a_2914_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2924_) == 0 {
                                    v_a_2925_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                                    crate::leanh::lean_inc(v_a_2925_);
                                    crate::leanh::lean_dec_ref_known(v___x_2924_, 1);
                                    v___x_2926_ = (crate::leanh::lean_unbox(v_a_2925_) as u8);
                                    crate::leanh::lean_dec(v_a_2925_);
                                    if v___x_2926_ == 0 {
                                        crate::leanh::lean_dec(v_a_2919_);
                                        v___x_2927_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHetero(v_a_2903_, v_b_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                                        return v___x_2927_;
                                    } else {
                                        v___x_2928_ = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateCtorHomo(v_a_2919_, v_a_2903_, v_b_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
                                        crate::leanh::lean_dec(v_a_2919_);
                                        return v___x_2928_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2919_);
                                    crate::leanh::lean_dec_ref(v_b_2904_);
                                    crate::leanh::lean_dec_ref(v_a_2903_);
                                    v_a_2929_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                                    v_isSharedCheck_2936_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2924_)) as u8;
                                    if v_isSharedCheck_2936_ == 0 {
                                        v___x_2931_ = v___x_2924_;
                                        v_isShared_2932_ = v_isSharedCheck_2936_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2929_);
                                        crate::leanh::lean_dec(v___x_2924_);
                                        v___x_2931_ = crate::leanh::lean_box(0);
                                        v_isShared_2932_ = v_isSharedCheck_2936_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2919_);
                                crate::leanh::lean_dec_ref(v_b_2904_);
                                crate::leanh::lean_dec_ref(v_a_2903_);
                                v_a_2937_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                                v_isSharedCheck_2944_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2922_)) as u8;
                                if v_isSharedCheck_2944_ == 0 {
                                    v___x_2939_ = v___x_2922_;
                                    v_isShared_2940_ = v_isSharedCheck_2944_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2937_);
                                    crate::leanh::lean_dec(v___x_2922_);
                                    v___x_2939_ = crate::leanh::lean_box(0);
                                    v_isShared_2940_ = v_isSharedCheck_2944_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2919_);
                            crate::leanh::lean_dec_ref(v_b_2904_);
                            crate::leanh::lean_dec_ref(v_a_2903_);
                            v_a_2945_ = crate::leanh::lean_ctor_get(v___x_2920_, 0);
                            v_isSharedCheck_2952_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2920_)) as u8;
                            if v_isSharedCheck_2952_ == 0 {
                                v___x_2947_ = v___x_2920_;
                                v_isShared_2948_ = v_isSharedCheck_2952_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2945_);
                                crate::leanh::lean_dec(v___x_2920_);
                                v___x_2947_ = crate::leanh::lean_box(0);
                                v_isShared_2948_ = v_isSharedCheck_2952_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2904_);
                        crate::leanh::lean_dec_ref(v_a_2903_);
                        v_a_2953_ = crate::leanh::lean_ctor_get(v___x_2918_, 0);
                        v_isSharedCheck_2960_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2918_)) as u8;
                        if v_isSharedCheck_2960_ == 0 {
                            v___x_2955_ = v___x_2918_;
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2953_);
                            crate::leanh::lean_dec(v___x_2918_);
                            v___x_2955_ = crate::leanh::lean_box(0);
                            v_isShared_2956_ = v_isSharedCheck_2960_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2904_);
                    crate::leanh::lean_dec_ref(v_a_2903_);
                    v_a_2961_ = crate::leanh::lean_ctor_get(v___x_2916_, 0);
                    v_isSharedCheck_2968_ = (!crate::leanh::lean_is_exclusive(v___x_2916_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v___x_2963_ = v___x_2916_;
                        v_isShared_2964_ = v_isSharedCheck_2968_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2961_);
                        crate::leanh::lean_dec(v___x_2916_);
                        v___x_2963_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
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
                    v_reuseFailAlloc_2943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
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
                    v_reuseFailAlloc_2951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
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
                    v_reuseFailAlloc_2959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
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
                    v_reuseFailAlloc_2967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
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
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_b_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
    mut v_a_2978_: *mut crate::leanh::LeanObject,
    mut v_a_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Lean_Meta_Grind_propagateCtor(
        v_a_2969_, v_b_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_,
        v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_,
    );
    crate::leanh::lean_dec(v_a_2980_);
    crate::leanh::lean_dec_ref(v_a_2979_);
    crate::leanh::lean_dec(v_a_2978_);
    crate::leanh::lean_dec_ref(v_a_2977_);
    crate::leanh::lean_dec(v_a_2976_);
    crate::leanh::lean_dec_ref(v_a_2975_);
    crate::leanh::lean_dec(v_a_2974_);
    crate::leanh::lean_dec_ref(v_a_2973_);
    crate::leanh::lean_dec(v_a_2972_);
    crate::leanh::lean_dec(v_a_2971_);
    return v_res_2982_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Ctor(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Ctor(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
}
