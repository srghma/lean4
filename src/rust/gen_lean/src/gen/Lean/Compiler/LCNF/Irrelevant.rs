// Lean compiler output
// Module: Lean.Compiler.LCNF.Irrelevant
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.Util
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_infer_type,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_to_int, lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_length, lean_uint64_of_nat,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::BaseTypes::{
    initialize_Lean_Compiler_LCNF_BaseTypes, l_Lean_Compiler_LCNF_getOtherDeclBaseType,
    runtime_initialize_Lean_Compiler_LCNF_BaseTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Expr_isErased;
use crate::r#gen::Lean::Compiler::LCNF::Util::{
    initialize_Lean_Compiler_LCNF_Util, l_Lean_Compiler_LCNF_isRuntimeBuiltinType,
    runtime_initialize_Lean_Compiler_LCNF_Util,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_instInhabitedCoreM___lam__0___boxed;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut leanh::LeanObject,72621647814721793 as *mut leanh::LeanObject,65793 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1: u64 = 0;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13_value: leanh::LeanStringObject<82> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 114, 114, 101, 108, 101, 118, 97, 110, 116, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 103, 101, 116, 82, 101, 108, 101, 118, 97, 110, 116, 67, 116, 111, 114, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 116, 111, 114, 78, 97, 109, 101, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10_value:
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
    m_data: [110, 117, 109, 80, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 105, 101, 108, 100, 73, 100, 120, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0(
    mut v_k_1374_: *mut leanh::LeanObject,
    mut v_b_1375_: *mut leanh::LeanObject,
    mut v_c_1376_: *mut leanh::LeanObject,
    mut v___y_1377_: *mut leanh::LeanObject,
    mut v___y_1378_: *mut leanh::LeanObject,
    mut v___y_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1380_);
    leanh::lean_inc_ref(v___y_1379_);
    leanh::lean_inc(v___y_1378_);
    leanh::lean_inc_ref(v___y_1377_);
    v___x_1382_ = leanh::lean_apply_7(
        v_k_1374_,
        v_b_1375_,
        v_c_1376_,
        v___y_1377_,
        v___y_1378_,
        v___y_1379_,
        v___y_1380_,
        leanh::lean_box(0),
    );
    return v___x_1382_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0___boxed(
    mut v_k_1383_: *mut leanh::LeanObject,
    mut v_b_1384_: *mut leanh::LeanObject,
    mut v_c_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0(v_k_1383_, v_b_1384_, v_c_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
    leanh::lean_dec(v___y_1389_);
    leanh::lean_dec_ref(v___y_1388_);
    leanh::lean_dec(v___y_1387_);
    leanh::lean_dec_ref(v___y_1386_);
    return v_res_1391_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(
    mut v_type_1392_: *mut leanh::LeanObject,
    mut v_k_1393_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1394_: u8,
    mut v_whnfType_1395_: u8,
    mut v___y_1396_: *mut leanh::LeanObject,
    mut v___y_1397_: *mut leanh::LeanObject,
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1401_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1401_, 0, v_k_1393_);
                v___x_1402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_1392_,
                    v___f_1401_,
                    v_cleanupAnnotations_1394_,
                    v_whnfType_1395_,
                    v___y_1396_,
                    v___y_1397_,
                    v___y_1398_,
                    v___y_1399_,
                );
                if leanh::lean_obj_tag(v___x_1402_) == 0 {
                    v_a_1403_ = leanh::lean_ctor_get(v___x_1402_, 0);
                    v_isSharedCheck_1410_ = (!leanh::lean_is_exclusive(v___x_1402_)) as u8;
                    if v_isSharedCheck_1410_ == 0 {
                        v___x_1405_ = v___x_1402_;
                        v_isShared_1406_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1403_);
                        leanh::lean_dec(v___x_1402_);
                        v___x_1405_ = leanh::lean_box(0);
                        v_isShared_1406_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1411_ = leanh::lean_ctor_get(v___x_1402_, 0);
                    v_isSharedCheck_1418_ = (!leanh::lean_is_exclusive(v___x_1402_)) as u8;
                    if v_isSharedCheck_1418_ == 0 {
                        v___x_1413_ = v___x_1402_;
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1411_);
                        leanh::lean_dec(v___x_1402_);
                        v___x_1413_ = leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 3;
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
                    v_reuseFailAlloc_1409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1408_;
            }
            3 => {
                if v_isShared_1414_ == 0 {
                    v___x_1416_ = v___x_1413_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
                    v___x_1416_ = v_reuseFailAlloc_1417_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___boxed(
    mut v_type_1419_: *mut leanh::LeanObject,
    mut v_k_1420_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1421_: *mut leanh::LeanObject,
    mut v_whnfType_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___y_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1428_: u8 = 0;
    let mut v_whnfType_boxed_1429_: u8 = 0;
    let mut v_res_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1428_ = (leanh::lean_unbox(v_cleanupAnnotations_1421_) as u8);
    v_whnfType_boxed_1429_ = (leanh::lean_unbox(v_whnfType_1422_) as u8);
    v_res_1430_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(v_type_1419_, v_k_1420_, v_cleanupAnnotations_boxed_1428_, v_whnfType_boxed_1429_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
    leanh::lean_dec(v___y_1426_);
    leanh::lean_dec_ref(v___y_1425_);
    leanh::lean_dec(v___y_1424_);
    leanh::lean_dec_ref(v___y_1423_);
    return v_res_1430_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2(
    mut v_00_u03b1_1431_: *mut leanh::LeanObject,
    mut v_type_1432_: *mut leanh::LeanObject,
    mut v_k_1433_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1434_: u8,
    mut v_whnfType_1435_: u8,
    mut v___y_1436_: *mut leanh::LeanObject,
    mut v___y_1437_: *mut leanh::LeanObject,
    mut v___y_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(v_type_1432_, v_k_1433_, v_cleanupAnnotations_1434_, v_whnfType_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
    return v___x_1441_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___boxed(
    mut v_00_u03b1_1442_: *mut leanh::LeanObject,
    mut v_type_1443_: *mut leanh::LeanObject,
    mut v_k_1444_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1445_: *mut leanh::LeanObject,
    mut v_whnfType_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1452_: u8 = 0;
    let mut v_whnfType_boxed_1453_: u8 = 0;
    let mut v_res_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1452_ = (leanh::lean_unbox(v_cleanupAnnotations_1445_) as u8);
    v_whnfType_boxed_1453_ = (leanh::lean_unbox(v_whnfType_1446_) as u8);
    v_res_1454_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2(v_00_u03b1_1442_, v_type_1443_, v_k_1444_, v_cleanupAnnotations_boxed_1452_, v_whnfType_boxed_1453_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    leanh::lean_dec(v___y_1450_);
    leanh::lean_dec_ref(v___y_1449_);
    leanh::lean_dec(v___y_1448_);
    leanh::lean_dec_ref(v___y_1447_);
    return v_res_1454_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3(
    mut v_msg_1456_: *mut leanh::LeanObject,
    mut v___y_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549__overap_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1460_ = l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0;
    v___x_2549__overap_1461_ = lean_panic_fn_borrowed(v___f_1460_, v_msg_1456_);
    leanh::lean_inc(v___y_1458_);
    leanh::lean_inc_ref(v___y_1457_);
    v___x_1462_ = leanh::lean_apply_3(
        v___x_2549__overap_1461_,
        v___y_1457_,
        v___y_1458_,
        leanh::lean_box(0),
    );
    return v___x_1462_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___boxed(
    mut v_msg_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
    mut v___y_1465_: *mut leanh::LeanObject,
    mut v___y_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3(v_msg_1463_, v___y_1464_, v___y_1465_);
    leanh::lean_dec(v___y_1465_);
    leanh::lean_dec_ref(v___y_1464_);
    return v_res_1467_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(
    mut v_trivialType_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_b_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: u8 = 0;
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_a_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1476_ = leanh::lean_ctor_get(v_a_1469_, 0);
                v_start_1477_ = leanh::lean_ctor_get(v_a_1469_, 1);
                v_stop_1478_ = leanh::lean_ctor_get(v_a_1469_, 2);
                v_isSharedCheck_1517_ = (!leanh::lean_is_exclusive(v_a_1469_)) as u8;
                if v_isSharedCheck_1517_ == 0 {
                    v___x_1480_ = v_a_1469_;
                    v_isShared_1481_ = v_isSharedCheck_1517_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_1478_);
                    leanh::lean_inc(v_start_1477_);
                    leanh::lean_inc(v_array_1476_);
                    leanh::lean_dec(v_a_1469_);
                    v___x_1480_ = leanh::lean_box(0);
                    v_isShared_1481_ = v_isSharedCheck_1517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1482_ = lean_nat_dec_lt(v_start_1477_, v_stop_1478_);
                if v___x_1482_ == 0 {
                    leanh::lean_del_object(v___x_1480_);
                    leanh::lean_dec(v_stop_1478_);
                    leanh::lean_dec(v_start_1477_);
                    leanh::lean_dec_ref(v_array_1476_);
                    leanh::lean_dec_ref(v_trivialType_1468_);
                    v___x_1483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1483_, 0, v_b_1470_);
                    return v___x_1483_;
                } else {
                    v___x_1484_ = lean_array_fget_borrowed(v_array_1476_, v_start_1477_);
                    leanh::lean_inc(v___y_1474_);
                    leanh::lean_inc_ref(v___y_1473_);
                    leanh::lean_inc(v___y_1472_);
                    leanh::lean_inc_ref(v___y_1471_);
                    leanh::lean_inc(v___x_1484_);
                    v___x_1485_ = lean_infer_type(
                        v___x_1484_,
                        v___y_1471_,
                        v___y_1472_,
                        v___y_1473_,
                        v___y_1474_,
                    );
                    if leanh::lean_obj_tag(v___x_1485_) == 0 {
                        v_a_1486_ = leanh::lean_ctor_get(v___x_1485_, 0);
                        leanh::lean_inc(v_a_1486_);
                        leanh::lean_dec_ref_known(v___x_1485_, 1);
                        leanh::lean_inc_ref(v_trivialType_1468_);
                        leanh::lean_inc(v___y_1474_);
                        leanh::lean_inc_ref(v___y_1473_);
                        leanh::lean_inc(v___y_1472_);
                        leanh::lean_inc_ref(v___y_1471_);
                        v___x_1487_ = leanh::lean_apply_6(
                            v_trivialType_1468_,
                            v_a_1486_,
                            v___y_1471_,
                            v___y_1472_,
                            v___y_1473_,
                            v___y_1474_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_1487_) == 0 {
                            v_a_1488_ = leanh::lean_ctor_get(v___x_1487_, 0);
                            leanh::lean_inc(v_a_1488_);
                            leanh::lean_dec_ref_known(v___x_1487_, 1);
                            v___x_1489_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1490_ = lean_nat_add(v_start_1477_, v___x_1489_);
                            leanh::lean_dec(v_start_1477_);
                            if v_isShared_1481_ == 0 {
                                leanh::lean_ctor_set(v___x_1480_, 1, v___x_1490_);
                                v___x_1492_ = v___x_1480_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1500_ =
                                    leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1500_,
                                    0,
                                    v_array_1476_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1490_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1500_,
                                    2,
                                    v_stop_1478_,
                                );
                                v___x_1492_ = v_reuseFailAlloc_1500_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1480_);
                            leanh::lean_dec(v_stop_1478_);
                            leanh::lean_dec(v_start_1477_);
                            leanh::lean_dec_ref(v_array_1476_);
                            leanh::lean_dec_ref(v_b_1470_);
                            leanh::lean_dec_ref(v_trivialType_1468_);
                            v_a_1501_ = leanh::lean_ctor_get(v___x_1487_, 0);
                            v_isSharedCheck_1508_ =
                                (!leanh::lean_is_exclusive(v___x_1487_)) as u8;
                            if v_isSharedCheck_1508_ == 0 {
                                v___x_1503_ = v___x_1487_;
                                v_isShared_1504_ = v_isSharedCheck_1508_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1501_);
                                leanh::lean_dec(v___x_1487_);
                                v___x_1503_ = leanh::lean_box(0);
                                v_isShared_1504_ = v_isSharedCheck_1508_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_1480_);
                        leanh::lean_dec(v_stop_1478_);
                        leanh::lean_dec(v_start_1477_);
                        leanh::lean_dec_ref(v_array_1476_);
                        leanh::lean_dec_ref(v_b_1470_);
                        leanh::lean_dec_ref(v_trivialType_1468_);
                        v_a_1509_ = leanh::lean_ctor_get(v___x_1485_, 0);
                        v_isSharedCheck_1516_ =
                            (!leanh::lean_is_exclusive(v___x_1485_)) as u8;
                        if v_isSharedCheck_1516_ == 0 {
                            v___x_1511_ = v___x_1485_;
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1509_);
                            leanh::lean_dec(v___x_1485_);
                            v___x_1511_ = leanh::lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1498_ = (leanh::lean_unbox(v_a_1488_) as u8);
                leanh::lean_dec(v_a_1488_);
                if v___x_1498_ == 0 {
                    v___y_1494_ = v___x_1482_;
                    state = 3;
                    continue;
                } else {
                    v___x_1499_ = 0;
                    v___y_1494_ = v___x_1499_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1495_ = leanh::lean_box((v___y_1494_) as usize);
                v___x_1496_ = lean_array_push(v_b_1470_, v___x_1495_);
                v_a_1469_ = v___x_1492_;
                v_b_1470_ = v___x_1496_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_1504_ == 0 {
                    v___x_1506_ = v___x_1503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1506_;
            }
            6 => {
                if v_isShared_1512_ == 0 {
                    v___x_1514_ = v___x_1511_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
                    v___x_1514_ = v_reuseFailAlloc_1515_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg___boxed(
    mut v_trivialType_1518_: *mut leanh::LeanObject,
    mut v_a_1519_: *mut leanh::LeanObject,
    mut v_b_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(v_trivialType_1518_, v_a_1519_, v_b_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    leanh::lean_dec(v___y_1524_);
    leanh::lean_dec_ref(v___y_1523_);
    leanh::lean_dec(v___y_1522_);
    leanh::lean_dec_ref(v___y_1521_);
    return v_res_1526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(
    mut v_trivialType_1529_: *mut leanh::LeanObject,
    mut v_numParams_1530_: *mut leanh::LeanObject,
    mut v_xs_1531_: *mut leanh::LeanObject,
    mut v_x_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1538_ = leanh::lean_unsigned_to_nat(0);
                v___x_1539_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0;
                v___x_1545_ = lean_array_get_size(v_xs_1531_);
                v___x_1546_ = lean_nat_dec_le(v_numParams_1530_, v___x_1538_);
                if v___x_1546_ == 0 {
                    v_lower_1541_ = v_numParams_1530_;
                    v_upper_1542_ = v___x_1545_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_numParams_1530_);
                    v_lower_1541_ = v___x_1538_;
                    v_upper_1542_ = v___x_1545_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1543_ = l_Array_toSubarray___redArg(v_xs_1531_, v_lower_1541_, v_upper_1542_);
                v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(v_trivialType_1529_, v___x_1543_, v___x_1539_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
                return v___x_1544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed(
    mut v_trivialType_1547_: *mut leanh::LeanObject,
    mut v_numParams_1548_: *mut leanh::LeanObject,
    mut v_xs_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
    mut v___y_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1556_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(v_trivialType_1547_, v_numParams_1548_, v_xs_1549_, v_x_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
    leanh::lean_dec(v___y_1554_);
    leanh::lean_dec_ref(v___y_1553_);
    leanh::lean_dec(v___y_1552_);
    leanh::lean_dec_ref(v___y_1551_);
    leanh::lean_dec_ref(v_x_1550_);
    return v_res_1556_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1557_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0);
    v___x_1559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1559_, 0, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1);
    v___x_1561_ = leanh::lean_unsigned_to_nat(0);
    v___x_1562_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1562_, 0, v___x_1561_);
    leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
    leanh::lean_ctor_set(v___x_1562_, 2, v___x_1561_);
    leanh::lean_ctor_set(v___x_1562_, 3, v___x_1561_);
    leanh::lean_ctor_set(v___x_1562_, 4, v___x_1560_);
    leanh::lean_ctor_set(v___x_1562_, 5, v___x_1560_);
    leanh::lean_ctor_set(v___x_1562_, 6, v___x_1560_);
    leanh::lean_ctor_set(v___x_1562_, 7, v___x_1560_);
    leanh::lean_ctor_set(v___x_1562_, 8, v___x_1560_);
    leanh::lean_ctor_set(v___x_1562_, 9, v___x_1560_);
    return v___x_1562_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = leanh::lean_unsigned_to_nat(32);
    v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
    v___x_1565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = 5usize;
    v___x_1567_ = leanh::lean_unsigned_to_nat(0);
    v___x_1568_ = leanh::lean_unsigned_to_nat(32);
    v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
    v___x_1570_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3);
    v___x_1571_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1571_, 0, v___x_1570_);
    leanh::lean_ctor_set(v___x_1571_, 1, v___x_1569_);
    leanh::lean_ctor_set(v___x_1571_, 2, v___x_1567_);
    leanh::lean_ctor_set(v___x_1571_, 3, v___x_1567_);
    leanh::lean_ctor_set_usize(v___x_1571_, 4, v___x_1566_);
    return v___x_1571_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = leanh::lean_box(1);
    v___x_1573_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4);
    v___x_1574_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1);
    v___x_1575_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
    leanh::lean_ctor_set(v___x_1575_, 1, v___x_1573_);
    leanh::lean_ctor_set(v___x_1575_, 2, v___x_1572_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10(
    mut v_msgData_1576_: *mut leanh::LeanObject,
    mut v___y_1577_: *mut leanh::LeanObject,
    mut v___y_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = lean_st_ref_get(v___y_1578_);
    v_env_1581_ = leanh::lean_ctor_get(v___x_1580_, 0);
    leanh::lean_inc_ref(v_env_1581_);
    leanh::lean_dec(v___x_1580_);
    v_options_1582_ = leanh::lean_ctor_get(v___y_1577_, 2);
    v___x_1583_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2);
    v___x_1584_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5);
    leanh::lean_inc_ref(v_options_1582_);
    v___x_1585_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1585_, 0, v_env_1581_);
    leanh::lean_ctor_set(v___x_1585_, 1, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 2, v___x_1584_);
    leanh::lean_ctor_set(v___x_1585_, 3, v_options_1582_);
    v___x_1586_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    leanh::lean_ctor_set(v___x_1586_, 1, v_msgData_1576_);
    v___x_1587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    return v___x_1587_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(
    mut v_msgData_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
    mut v___y_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_1588_, v___y_1589_, v___y_1590_);
    leanh::lean_dec(v___y_1590_);
    leanh::lean_dec_ref(v___y_1589_);
    return v_res_1592_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(
    mut v_msg_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1597_ = leanh::lean_ctor_get(v___y_1594_, 5);
                v___x_1598_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10(v_msg_1593_, v___y_1594_, v___y_1595_);
                v_a_1599_ = leanh::lean_ctor_get(v___x_1598_, 0);
                v_isSharedCheck_1607_ = (!leanh::lean_is_exclusive(v___x_1598_)) as u8;
                if v_isSharedCheck_1607_ == 0 {
                    v___x_1601_ = v___x_1598_;
                    v_isShared_1602_ = v_isSharedCheck_1607_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1599_);
                    leanh::lean_dec(v___x_1598_);
                    v___x_1601_ = leanh::lean_box(0);
                    v_isShared_1602_ = v_isSharedCheck_1607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1597_);
                v___x_1603_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1603_, 0, v_ref_1597_);
                leanh::lean_ctor_set(v___x_1603_, 1, v_a_1599_);
                if v_isShared_1602_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1601_, 1);
                    leanh::lean_ctor_set(v___x_1601_, 0, v___x_1603_);
                    v___x_1605_ = v___x_1601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
                    v___x_1605_ = v_reuseFailAlloc_1606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_msg_1608_: *mut leanh::LeanObject,
    mut v___y_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1608_, v___y_1609_, v___y_1610_);
    leanh::lean_dec(v___y_1610_);
    leanh::lean_dec_ref(v___y_1609_);
    return v_res_1612_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(
    mut v_ref_1613_: *mut leanh::LeanObject,
    mut v_msg_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1630_: u8 = 0;
    let mut v_cancelTk_x3f_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1632_: u8 = 0;
    let mut v_inheritedTraceOptions_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1618_ = leanh::lean_ctor_get(v___y_1615_, 0);
    v_fileMap_1619_ = leanh::lean_ctor_get(v___y_1615_, 1);
    v_options_1620_ = leanh::lean_ctor_get(v___y_1615_, 2);
    v_currRecDepth_1621_ = leanh::lean_ctor_get(v___y_1615_, 3);
    v_maxRecDepth_1622_ = leanh::lean_ctor_get(v___y_1615_, 4);
    v_ref_1623_ = leanh::lean_ctor_get(v___y_1615_, 5);
    v_currNamespace_1624_ = leanh::lean_ctor_get(v___y_1615_, 6);
    v_openDecls_1625_ = leanh::lean_ctor_get(v___y_1615_, 7);
    v_initHeartbeats_1626_ = leanh::lean_ctor_get(v___y_1615_, 8);
    v_maxHeartbeats_1627_ = leanh::lean_ctor_get(v___y_1615_, 9);
    v_quotContext_1628_ = leanh::lean_ctor_get(v___y_1615_, 10);
    v_currMacroScope_1629_ = leanh::lean_ctor_get(v___y_1615_, 11);
    v_diag_1630_ = leanh::lean_ctor_get_uint8(
        v___y_1615_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1631_ = leanh::lean_ctor_get(v___y_1615_, 12);
    v_suppressElabErrors_1632_ = leanh::lean_ctor_get_uint8(
        v___y_1615_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1633_ = leanh::lean_ctor_get(v___y_1615_, 13);
    v_ref_1634_ = l_Lean_replaceRef(v_ref_1613_, v_ref_1623_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1633_);
    leanh::lean_inc(v_cancelTk_x3f_1631_);
    leanh::lean_inc(v_currMacroScope_1629_);
    leanh::lean_inc(v_quotContext_1628_);
    leanh::lean_inc(v_maxHeartbeats_1627_);
    leanh::lean_inc(v_initHeartbeats_1626_);
    leanh::lean_inc(v_openDecls_1625_);
    leanh::lean_inc(v_currNamespace_1624_);
    leanh::lean_inc(v_maxRecDepth_1622_);
    leanh::lean_inc(v_currRecDepth_1621_);
    leanh::lean_inc_ref(v_options_1620_);
    leanh::lean_inc_ref(v_fileMap_1619_);
    leanh::lean_inc_ref(v_fileName_1618_);
    v___x_1635_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1635_, 0, v_fileName_1618_);
    leanh::lean_ctor_set(v___x_1635_, 1, v_fileMap_1619_);
    leanh::lean_ctor_set(v___x_1635_, 2, v_options_1620_);
    leanh::lean_ctor_set(v___x_1635_, 3, v_currRecDepth_1621_);
    leanh::lean_ctor_set(v___x_1635_, 4, v_maxRecDepth_1622_);
    leanh::lean_ctor_set(v___x_1635_, 5, v_ref_1634_);
    leanh::lean_ctor_set(v___x_1635_, 6, v_currNamespace_1624_);
    leanh::lean_ctor_set(v___x_1635_, 7, v_openDecls_1625_);
    leanh::lean_ctor_set(v___x_1635_, 8, v_initHeartbeats_1626_);
    leanh::lean_ctor_set(v___x_1635_, 9, v_maxHeartbeats_1627_);
    leanh::lean_ctor_set(v___x_1635_, 10, v_quotContext_1628_);
    leanh::lean_ctor_set(v___x_1635_, 11, v_currMacroScope_1629_);
    leanh::lean_ctor_set(v___x_1635_, 12, v_cancelTk_x3f_1631_);
    leanh::lean_ctor_set(v___x_1635_, 13, v_inheritedTraceOptions_1633_);
    leanh::lean_ctor_set_uint8(
        v___x_1635_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1630_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1635_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1632_,
    );
    v___x_1636_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1614_, v___x_1635_, v___y_1616_);
    leanh::lean_dec_ref_known(v___x_1635_, 14);
    return v___x_1636_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_ref_1637_: *mut leanh::LeanObject,
    mut v_msg_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(v_ref_1637_, v_msg_1638_, v___y_1639_, v___y_1640_);
    leanh::lean_dec(v___y_1640_);
    leanh::lean_dec_ref(v___y_1639_);
    leanh::lean_dec(v_ref_1637_);
    return v_res_1642_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0;
    v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2;
    v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4;
    v___x_1651_ = l_Lean_stringToMessageData(v___x_1650_);
    return v___x_1651_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_1654_ = l_Lean_stringToMessageData(v___x_1653_);
    return v___x_1654_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
    return v___x_1657_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(
    mut v_msg_1664_: *mut leanh::LeanObject,
    mut v_declHint_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u8 = 0;
    let mut v_isExporting_1671_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = lean_st_ref_get(v___y_1666_);
                v_env_1669_ = leanh::lean_ctor_get(v___x_1668_, 0);
                leanh::lean_inc_ref(v_env_1669_);
                leanh::lean_dec(v___x_1668_);
                v___x_1670_ = l_Lean_Name_isAnonymous(v_declHint_1665_);
                if v___x_1670_ == 0 {
                    v_isExporting_1671_ = leanh::lean_ctor_get_uint8(
                        v_env_1669_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1671_ == 0 {
                        leanh::lean_dec_ref(v_env_1669_);
                        leanh::lean_dec(v_declHint_1665_);
                        v___x_1672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1672_, 0, v_msg_1664_);
                        return v___x_1672_;
                    } else {
                        leanh::lean_inc_ref(v_env_1669_);
                        v___x_1673_ = l_Lean_Environment_setExporting(v_env_1669_, v___x_1670_);
                        leanh::lean_inc(v_declHint_1665_);
                        leanh::lean_inc_ref(v___x_1673_);
                        v___x_1674_ = l_Lean_Environment_contains(
                            v___x_1673_,
                            v_declHint_1665_,
                            v_isExporting_1671_,
                        );
                        if v___x_1674_ == 0 {
                            leanh::lean_dec_ref(v___x_1673_);
                            leanh::lean_dec_ref(v_env_1669_);
                            leanh::lean_dec(v_declHint_1665_);
                            v___x_1675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1675_, 0, v_msg_1664_);
                            return v___x_1675_;
                        } else {
                            v___x_1676_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2);
                            v___x_1677_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5);
                            v___x_1678_ = l_Lean_Options_empty;
                            v___x_1679_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1679_, 0, v___x_1673_);
                            leanh::lean_ctor_set(v___x_1679_, 1, v___x_1676_);
                            leanh::lean_ctor_set(v___x_1679_, 2, v___x_1677_);
                            leanh::lean_ctor_set(v___x_1679_, 3, v___x_1678_);
                            leanh::lean_inc(v_declHint_1665_);
                            v___x_1680_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1665_, v___x_1670_);
                            v_c_1681_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1681_, 0, v___x_1679_);
                            leanh::lean_ctor_set(v_c_1681_, 1, v___x_1680_);
                            v___x_1682_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1669_,
                                v_declHint_1665_,
                            );
                            if leanh::lean_obj_tag(v___x_1682_) == 0 {
                                leanh::lean_dec_ref(v_env_1669_);
                                leanh::lean_dec(v_declHint_1665_);
                                v___x_1683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
                                v___x_1684_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1684_, 0, v___x_1683_);
                                leanh::lean_ctor_set(v___x_1684_, 1, v_c_1681_);
                                v___x_1685_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
                                v___x_1686_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1686_, 0, v___x_1684_);
                                leanh::lean_ctor_set(v___x_1686_, 1, v___x_1685_);
                                v___x_1687_ = l_Lean_MessageData_note(v___x_1686_);
                                v___x_1688_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1688_, 0, v_msg_1664_);
                                leanh::lean_ctor_set(v___x_1688_, 1, v___x_1687_);
                                v___x_1689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
                                return v___x_1689_;
                            } else {
                                v_val_1690_ = leanh::lean_ctor_get(v___x_1682_, 0);
                                v_isSharedCheck_1725_ =
                                    (!leanh::lean_is_exclusive(v___x_1682_)) as u8;
                                if v_isSharedCheck_1725_ == 0 {
                                    v___x_1692_ = v___x_1682_;
                                    v_isShared_1693_ = v_isSharedCheck_1725_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1690_);
                                    leanh::lean_dec(v___x_1682_);
                                    v___x_1692_ = leanh::lean_box(0);
                                    v_isShared_1693_ = v_isSharedCheck_1725_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1669_);
                    leanh::lean_dec(v_declHint_1665_);
                    v___x_1726_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1726_, 0, v_msg_1664_);
                    return v___x_1726_;
                }
            }
            1 => {
                v___x_1694_ = leanh::lean_box(0);
                v___x_1695_ = l_Lean_Environment_header(v_env_1669_);
                leanh::lean_dec_ref(v_env_1669_);
                v___x_1696_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1695_);
                v_mod_1697_ = lean_array_get(v___x_1694_, v___x_1696_, v_val_1690_);
                leanh::lean_dec(v_val_1690_);
                leanh::lean_dec_ref(v___x_1696_);
                v___x_1698_ = l_Lean_isPrivateName(v_declHint_1665_);
                leanh::lean_dec(v_declHint_1665_);
                if v___x_1698_ == 0 {
                    v___x_1699_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
                    v___x_1700_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1700_, 0, v___x_1699_);
                    leanh::lean_ctor_set(v___x_1700_, 1, v_c_1681_);
                    v___x_1701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_1702_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1702_, 0, v___x_1700_);
                    leanh::lean_ctor_set(v___x_1702_, 1, v___x_1701_);
                    v___x_1703_ = l_Lean_MessageData_ofName(v_mod_1697_);
                    v___x_1704_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1704_, 0, v___x_1702_);
                    leanh::lean_ctor_set(v___x_1704_, 1, v___x_1703_);
                    v___x_1705_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
                    v___x_1706_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1706_, 0, v___x_1704_);
                    leanh::lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                    v___x_1707_ = l_Lean_MessageData_note(v___x_1706_);
                    v___x_1708_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1708_, 0, v_msg_1664_);
                    leanh::lean_ctor_set(v___x_1708_, 1, v___x_1707_);
                    if v_isShared_1693_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1692_, 0);
                        leanh::lean_ctor_set(v___x_1692_, 0, v___x_1708_);
                        v___x_1710_ = v___x_1692_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1711_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
                    v___x_1713_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1713_, 0, v___x_1712_);
                    leanh::lean_ctor_set(v___x_1713_, 1, v_c_1681_);
                    v___x_1714_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_1715_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1715_, 0, v___x_1713_);
                    leanh::lean_ctor_set(v___x_1715_, 1, v___x_1714_);
                    v___x_1716_ = l_Lean_MessageData_ofName(v_mod_1697_);
                    v___x_1717_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1717_, 0, v___x_1715_);
                    leanh::lean_ctor_set(v___x_1717_, 1, v___x_1716_);
                    v___x_1718_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_1719_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1719_, 0, v___x_1717_);
                    leanh::lean_ctor_set(v___x_1719_, 1, v___x_1718_);
                    v___x_1720_ = l_Lean_MessageData_note(v___x_1719_);
                    v___x_1721_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1721_, 0, v_msg_1664_);
                    leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                    if v_isShared_1693_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1692_, 0);
                        leanh::lean_ctor_set(v___x_1692_, 0, v___x_1721_);
                        v___x_1723_ = v___x_1692_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1724_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
                        v___x_1723_ = v_reuseFailAlloc_1724_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1710_;
            }
            3 => {
                return v___x_1723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_1727_: *mut leanh::LeanObject,
    mut v_declHint_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1727_, v_declHint_1728_, v___y_1729_);
    leanh::lean_dec(v___y_1729_);
    return v_res_1731_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6(
    mut v_msg_1732_: *mut leanh::LeanObject,
    mut v_declHint_1733_: *mut leanh::LeanObject,
    mut v___y_1734_: *mut leanh::LeanObject,
    mut v___y_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1732_, v_declHint_1733_, v___y_1735_);
                v_a_1738_ = leanh::lean_ctor_get(v___x_1737_, 0);
                v_isSharedCheck_1747_ = (!leanh::lean_is_exclusive(v___x_1737_)) as u8;
                if v_isSharedCheck_1747_ == 0 {
                    v___x_1740_ = v___x_1737_;
                    v_isShared_1741_ = v_isSharedCheck_1747_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1738_);
                    leanh::lean_dec(v___x_1737_);
                    v___x_1740_ = leanh::lean_box(0);
                    v_isShared_1741_ = v_isSharedCheck_1747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1742_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1743_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                leanh::lean_ctor_set(v___x_1743_, 1, v_a_1738_);
                if v_isShared_1741_ == 0 {
                    leanh::lean_ctor_set(v___x_1740_, 0, v___x_1743_);
                    v___x_1745_ = v___x_1740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6___boxed(
    mut v_msg_1748_: *mut leanh::LeanObject,
    mut v_declHint_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6(v_msg_1748_, v_declHint_1749_, v___y_1750_, v___y_1751_);
    leanh::lean_dec(v___y_1751_);
    leanh::lean_dec_ref(v___y_1750_);
    return v_res_1753_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(
    mut v_ref_1754_: *mut leanh::LeanObject,
    mut v_msg_1755_: *mut leanh::LeanObject,
    mut v_declHint_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6(v_msg_1755_, v_declHint_1756_, v___y_1757_, v___y_1758_);
    v_a_1761_ = leanh::lean_ctor_get(v___x_1760_, 0);
    leanh::lean_inc(v_a_1761_);
    leanh::lean_dec_ref(v___x_1760_);
    v___x_1762_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(v_ref_1754_, v_a_1761_, v___y_1757_, v___y_1758_);
    return v___x_1762_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg___boxed(
    mut v_ref_1763_: *mut leanh::LeanObject,
    mut v_msg_1764_: *mut leanh::LeanObject,
    mut v_declHint_1765_: *mut leanh::LeanObject,
    mut v___y_1766_: *mut leanh::LeanObject,
    mut v___y_1767_: *mut leanh::LeanObject,
    mut v___y_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(v_ref_1763_, v_msg_1764_, v_declHint_1765_, v___y_1766_, v___y_1767_);
    leanh::lean_dec(v___y_1767_);
    leanh::lean_dec_ref(v___y_1766_);
    leanh::lean_dec(v_ref_1763_);
    return v_res_1769_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
    return v___x_1772_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(
    mut v_ref_1776_: *mut leanh::LeanObject,
    mut v_constName_1777_: *mut leanh::LeanObject,
    mut v___y_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_1782_ = 0;
    leanh::lean_inc(v_constName_1777_);
    v___x_1783_ = l_Lean_MessageData_ofConstName(v_constName_1777_, v___x_1782_);
    v___x_1784_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1781_);
    leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
    v___x_1785_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_1786_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1786_, 0, v___x_1784_);
    leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
    v___x_1787_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(v_ref_1776_, v___x_1786_, v_constName_1777_, v___y_1778_, v___y_1779_);
    return v___x_1787_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_1788_: *mut leanh::LeanObject,
    mut v_constName_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1793_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(v_ref_1788_, v_constName_1789_, v___y_1790_, v___y_1791_);
    leanh::lean_dec(v___y_1791_);
    leanh::lean_dec_ref(v___y_1790_);
    leanh::lean_dec(v_ref_1788_);
    return v_res_1793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(
    mut v_constName_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1798_ = leanh::lean_ctor_get(v___y_1795_, 5);
    v___x_1799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(v_ref_1798_, v_constName_1794_, v___y_1795_, v___y_1796_);
    return v___x_1799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg___boxed(
    mut v_constName_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(v_constName_1800_, v___y_1801_, v___y_1802_);
    leanh::lean_dec(v___y_1802_);
    leanh::lean_dec_ref(v___y_1801_);
    return v_res_1804_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(
    mut v_constName_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1809_ = lean_st_ref_get(v___y_1807_);
                v_env_1810_ = leanh::lean_ctor_get(v___x_1809_, 0);
                leanh::lean_inc_ref(v_env_1810_);
                leanh::lean_dec(v___x_1809_);
                v___x_1811_ = 0;
                leanh::lean_inc(v_constName_1805_);
                v___x_1812_ =
                    l_Lean_Environment_find_x3f(v_env_1810_, v_constName_1805_, v___x_1811_);
                if leanh::lean_obj_tag(v___x_1812_) == 0 {
                    v___x_1813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(v_constName_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1813_;
                } else {
                    leanh::lean_dec(v_constName_1805_);
                    v_val_1814_ = leanh::lean_ctor_get(v___x_1812_, 0);
                    v_isSharedCheck_1821_ = (!leanh::lean_is_exclusive(v___x_1812_)) as u8;
                    if v_isSharedCheck_1821_ == 0 {
                        v___x_1816_ = v___x_1812_;
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1814_);
                        leanh::lean_dec(v___x_1812_);
                        v___x_1816_ = leanh::lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1817_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1816_, 0);
                    v___x_1819_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_val_1814_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___boxed(
    mut v_constName_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(v_constName_1822_, v___y_1823_, v___y_1824_);
    leanh::lean_dec(v___y_1824_);
    leanh::lean_dec_ref(v___y_1823_);
    return v_res_1826_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1()
-> u64 {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u64 = 0;
    v___x_1833_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
    v___x_1834_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1835_: u64 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1);
    v___x_1836_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
    v___x_1837_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_1837_, 0, v___x_1836_);
    leanh::lean_ctor_set_uint64(
        v___x_1837_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1835_,
    );
    return v___x_1837_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1838_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3);
    v___x_1840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1840_, 0, v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = leanh::lean_box(1);
    v___x_1842_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4);
    v___x_1843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1844_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1844_, 0, v___x_1843_);
    leanh::lean_ctor_set(v___x_1844_, 1, v___x_1842_);
    leanh::lean_ctor_set(v___x_1844_, 2, v___x_1841_);
    return v___x_1844_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = 1;
    v___x_1848_ = leanh::lean_unsigned_to_nat(0);
    v___x_1849_ = leanh::lean_box(0);
    v___x_1850_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
    v___x_1851_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5);
    v___x_1852_ = leanh::lean_box(1);
    v___x_1853_ = 0;
    v___x_1854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2);
    v___x_1855_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
    leanh::lean_ctor_set(v___x_1855_, 1, v___x_1852_);
    leanh::lean_ctor_set(v___x_1855_, 2, v___x_1851_);
    leanh::lean_ctor_set(v___x_1855_, 3, v___x_1850_);
    leanh::lean_ctor_set(v___x_1855_, 4, v___x_1849_);
    leanh::lean_ctor_set(v___x_1855_, 5, v___x_1848_);
    leanh::lean_ctor_set(v___x_1855_, 6, v___x_1849_);
    leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_1853_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v___x_1853_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v___x_1853_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v___x_1847_,
    );
    return v___x_1855_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1857_ = leanh::lean_unsigned_to_nat(0);
    v___x_1858_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1858_, 0, v___x_1857_);
    leanh::lean_ctor_set(v___x_1858_, 1, v___x_1857_);
    leanh::lean_ctor_set(v___x_1858_, 2, v___x_1857_);
    leanh::lean_ctor_set(v___x_1858_, 3, v___x_1857_);
    leanh::lean_ctor_set(v___x_1858_, 4, v___x_1856_);
    leanh::lean_ctor_set(v___x_1858_, 5, v___x_1856_);
    leanh::lean_ctor_set(v___x_1858_, 6, v___x_1856_);
    leanh::lean_ctor_set(v___x_1858_, 7, v___x_1856_);
    leanh::lean_ctor_set(v___x_1858_, 8, v___x_1856_);
    leanh::lean_ctor_set(v___x_1858_, 9, v___x_1856_);
    return v___x_1858_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1860_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    leanh::lean_ctor_set(v___x_1860_, 1, v___x_1859_);
    leanh::lean_ctor_set(v___x_1860_, 2, v___x_1859_);
    leanh::lean_ctor_set(v___x_1860_, 3, v___x_1859_);
    leanh::lean_ctor_set(v___x_1860_, 4, v___x_1859_);
    leanh::lean_ctor_set(v___x_1860_, 5, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1862_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
    leanh::lean_ctor_set(v___x_1862_, 2, v___x_1861_);
    leanh::lean_ctor_set(v___x_1862_, 3, v___x_1861_);
    leanh::lean_ctor_set(v___x_1862_, 4, v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10);
    v___x_1864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4);
    v___x_1865_ = leanh::lean_box(1);
    v___x_1866_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9);
    v___x_1867_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8);
    v___x_1868_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    leanh::lean_ctor_set(v___x_1868_, 1, v___x_1866_);
    leanh::lean_ctor_set(v___x_1868_, 2, v___x_1865_);
    leanh::lean_ctor_set(v___x_1868_, 3, v___x_1864_);
    leanh::lean_ctor_set(v___x_1868_, 4, v___x_1863_);
    return v___x_1868_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
    v___x_1873_ = leanh::lean_unsigned_to_nat(47);
    v___x_1874_ = leanh::lean_unsigned_to_nat(21);
    v___x_1875_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
    v___x_1876_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
    v___x_1877_ = l_mkPanicMessageWithDecl(
        v___x_1876_,
        v___x_1875_,
        v___x_1874_,
        v___x_1873_,
        v___x_1872_,
    );
    return v___x_1877_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields(
    mut v_ctorName_1878_: *mut leanh::LeanObject,
    mut v_trivialType_1879_: *mut leanh::LeanObject,
    mut v_a_1880_: *mut leanh::LeanObject,
    mut v_a_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(v_ctorName_1878_, v_a_1880_, v_a_1881_);
                if leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = leanh::lean_ctor_get(v___x_1883_, 0);
                    leanh::lean_inc(v_a_1884_);
                    leanh::lean_dec_ref_known(v___x_1883_, 1);
                    if leanh::lean_obj_tag(v_a_1884_) == 6 {
                        v_val_1885_ = leanh::lean_ctor_get(v_a_1884_, 0);
                        leanh::lean_inc_ref(v_val_1885_);
                        leanh::lean_dec_ref_known(v_a_1884_, 1);
                        v___x_1886_ = 0;
                        v___x_1887_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7);
                        v___x_1888_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11);
                        v___x_1889_ = lean_st_mk_ref(v___x_1888_);
                        v_toConstantVal_1890_ = leanh::lean_ctor_get(v_val_1885_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_1890_);
                        v_numParams_1891_ = leanh::lean_ctor_get(v_val_1885_, 3);
                        leanh::lean_inc(v_numParams_1891_);
                        leanh::lean_dec_ref(v_val_1885_);
                        v_type_1892_ = leanh::lean_ctor_get(v_toConstantVal_1890_, 2);
                        leanh::lean_inc_ref(v_type_1892_);
                        leanh::lean_dec_ref(v_toConstantVal_1890_);
                        v___f_1893_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                        leanh::lean_closure_set(v___f_1893_, 0, v_trivialType_1879_);
                        leanh::lean_closure_set(v___f_1893_, 1, v_numParams_1891_);
                        v___x_1894_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(v_type_1892_, v___f_1893_, v___x_1886_, v___x_1886_, v___x_1887_, v___x_1889_, v_a_1880_, v_a_1881_);
                        if leanh::lean_obj_tag(v___x_1894_) == 0 {
                            v_a_1895_ = leanh::lean_ctor_get(v___x_1894_, 0);
                            v_isSharedCheck_1903_ =
                                (!leanh::lean_is_exclusive(v___x_1894_)) as u8;
                            if v_isSharedCheck_1903_ == 0 {
                                v___x_1897_ = v___x_1894_;
                                v_isShared_1898_ = v_isSharedCheck_1903_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1895_);
                                leanh::lean_dec(v___x_1894_);
                                v___x_1897_ = leanh::lean_box(0);
                                v_isShared_1898_ = v_isSharedCheck_1903_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_1889_);
                            return v___x_1894_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1884_);
                        leanh::lean_dec_ref(v_trivialType_1879_);
                        v___x_1904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15);
                        v___x_1905_ = l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3(v___x_1904_, v_a_1880_, v_a_1881_);
                        return v___x_1905_;
                    }
                } else {
                    leanh::lean_dec_ref(v_trivialType_1879_);
                    v_a_1906_ = leanh::lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1913_ = (!leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1908_ = v___x_1883_;
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1906_);
                        leanh::lean_dec(v___x_1883_);
                        v___x_1908_ = leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1899_ = lean_st_ref_get(v___x_1889_);
                leanh::lean_dec(v___x_1889_);
                leanh::lean_dec(v___x_1899_);
                if v_isShared_1898_ == 0 {
                    v___x_1901_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1895_);
                    v___x_1901_ = v_reuseFailAlloc_1902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1901_;
            }
            3 => {
                if v_isShared_1909_ == 0 {
                    v___x_1911_ = v___x_1908_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
                    v___x_1911_ = v_reuseFailAlloc_1912_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___boxed(
    mut v_ctorName_1914_: *mut leanh::LeanObject,
    mut v_trivialType_1915_: *mut leanh::LeanObject,
    mut v_a_1916_: *mut leanh::LeanObject,
    mut v_a_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ =
        l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields(
            v_ctorName_1914_,
            v_trivialType_1915_,
            v_a_1916_,
            v_a_1917_,
        );
    leanh::lean_dec(v_a_1917_);
    leanh::lean_dec_ref(v_a_1916_);
    return v_res_1919_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(
    mut v_trivialType_1920_: *mut leanh::LeanObject,
    mut v_inst_1921_: *mut leanh::LeanObject,
    mut v_R_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
    mut v_b_1924_: *mut leanh::LeanObject,
    mut v_c_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(v_trivialType_1920_, v_a_1923_, v_b_1924_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
    return v___x_1931_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___boxed(
    mut v_trivialType_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_R_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_b_1936_: *mut leanh::LeanObject,
    mut v_c_1937_: *mut leanh::LeanObject,
    mut v___y_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(v_trivialType_1932_, v_inst_1933_, v_R_1934_, v_a_1935_, v_b_1936_, v_c_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
    leanh::lean_dec(v___y_1941_);
    leanh::lean_dec_ref(v___y_1940_);
    leanh::lean_dec(v___y_1939_);
    leanh::lean_dec_ref(v___y_1938_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0(
    mut v_00_u03b1_1944_: *mut leanh::LeanObject,
    mut v_constName_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(v_constName_1945_, v___y_1946_, v___y_1947_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___boxed(
    mut v_00_u03b1_1950_: *mut leanh::LeanObject,
    mut v_constName_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0(v_00_u03b1_1950_, v_constName_1951_, v___y_1952_, v___y_1953_);
    leanh::lean_dec(v___y_1953_);
    leanh::lean_dec_ref(v___y_1952_);
    return v_res_1955_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3(
    mut v_00_u03b1_1956_: *mut leanh::LeanObject,
    mut v_ref_1957_: *mut leanh::LeanObject,
    mut v_constName_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(v_ref_1957_, v_constName_1958_, v___y_1959_, v___y_1960_);
    return v___x_1962_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_1963_: *mut leanh::LeanObject,
    mut v_ref_1964_: *mut leanh::LeanObject,
    mut v_constName_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3(v_00_u03b1_1963_, v_ref_1964_, v_constName_1965_, v___y_1966_, v___y_1967_);
    leanh::lean_dec(v___y_1967_);
    leanh::lean_dec_ref(v___y_1966_);
    leanh::lean_dec(v_ref_1964_);
    return v_res_1969_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5(
    mut v_00_u03b1_1970_: *mut leanh::LeanObject,
    mut v_ref_1971_: *mut leanh::LeanObject,
    mut v_msg_1972_: *mut leanh::LeanObject,
    mut v_declHint_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(v_ref_1971_, v_msg_1972_, v_declHint_1973_, v___y_1974_, v___y_1975_);
    return v___x_1977_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___boxed(
    mut v_00_u03b1_1978_: *mut leanh::LeanObject,
    mut v_ref_1979_: *mut leanh::LeanObject,
    mut v_msg_1980_: *mut leanh::LeanObject,
    mut v_declHint_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1985_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5(v_00_u03b1_1978_, v_ref_1979_, v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_);
    leanh::lean_dec(v___y_1983_);
    leanh::lean_dec_ref(v___y_1982_);
    leanh::lean_dec(v_ref_1979_);
    return v_res_1985_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7(
    mut v_msg_1986_: *mut leanh::LeanObject,
    mut v_declHint_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1986_, v_declHint_1987_, v___y_1989_);
    return v___x_1991_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___boxed(
    mut v_msg_1992_: *mut leanh::LeanObject,
    mut v_declHint_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7(v_msg_1992_, v_declHint_1993_, v___y_1994_, v___y_1995_);
    leanh::lean_dec(v___y_1995_);
    leanh::lean_dec_ref(v___y_1994_);
    return v_res_1997_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7(
    mut v_00_u03b1_1998_: *mut leanh::LeanObject,
    mut v_ref_1999_: *mut leanh::LeanObject,
    mut v_msg_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(v_ref_1999_, v_msg_2000_, v___y_2001_, v___y_2002_);
    return v___x_2004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_2005_: *mut leanh::LeanObject,
    mut v_ref_2006_: *mut leanh::LeanObject,
    mut v_msg_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
    mut v___y_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7(v_00_u03b1_2005_, v_ref_2006_, v_msg_2007_, v___y_2008_, v___y_2009_);
    leanh::lean_dec(v___y_2009_);
    leanh::lean_dec_ref(v___y_2008_);
    leanh::lean_dec(v_ref_2006_);
    return v_res_2011_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(
    mut v_00_u03b1_2012_: *mut leanh::LeanObject,
    mut v_msg_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_2013_, v___y_2014_, v___y_2015_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_2018_: *mut leanh::LeanObject,
    mut v_msg_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2023_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_2018_, v_msg_2019_, v___y_2020_, v___y_2021_);
    leanh::lean_dec(v___y_2021_);
    leanh::lean_dec_ref(v___y_2020_);
    return v_res_2023_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr_spec__0(
    mut v_a_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = lean_nat_to_int(v_a_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = leanh::lean_unsigned_to_nat(12);
    v___x_2045_ = lean_nat_to_int(v___x_2044_);
    return v___x_2045_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = leanh::lean_unsigned_to_nat(13);
    v___x_2053_ = lean_nat_to_int(v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0;
    v___x_2059_ = lean_string_length(v___x_2058_);
    return v___x_2059_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16,
    );
    v___x_2061_ = lean_nat_to_int(v___x_2060_);
    return v___x_2061_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg(
    mut v_x_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctorName_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldIdx_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctorName_2067_ = leanh::lean_ctor_get(v_x_2066_, 0);
    leanh::lean_inc(v_ctorName_2067_);
    v_numParams_2068_ = leanh::lean_ctor_get(v_x_2066_, 1);
    leanh::lean_inc(v_numParams_2068_);
    v_fieldIdx_2069_ = leanh::lean_ctor_get(v_x_2066_, 2);
    leanh::lean_inc(v_fieldIdx_2069_);
    leanh::lean_dec_ref(v_x_2066_);
    v___x_2070_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5;
    v___x_2071_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6;
    v___x_2072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7,
    );
    v___x_2073_ = leanh::lean_unsigned_to_nat(0);
    v___x_2074_ = l_Lean_Name_reprPrec(v_ctorName_2067_, v___x_2073_);
    v___x_2075_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2075_, 0, v___x_2072_);
    leanh::lean_ctor_set(v___x_2075_, 1, v___x_2074_);
    v___x_2076_ = 0;
    v___x_2077_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2077_, 0, v___x_2075_);
    leanh::lean_ctor_set_uint8(
        v___x_2077_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    v___x_2078_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2078_, 0, v___x_2071_);
    leanh::lean_ctor_set(v___x_2078_, 1, v___x_2077_);
    v___x_2079_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9;
    v___x_2080_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2080_, 0, v___x_2078_);
    leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
    v___x_2081_ = leanh::lean_box(1);
    v___x_2082_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2082_, 0, v___x_2080_);
    leanh::lean_ctor_set(v___x_2082_, 1, v___x_2081_);
    v___x_2083_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11;
    v___x_2084_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2084_, 0, v___x_2082_);
    leanh::lean_ctor_set(v___x_2084_, 1, v___x_2083_);
    v___x_2085_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2085_, 0, v___x_2084_);
    leanh::lean_ctor_set(v___x_2085_, 1, v___x_2070_);
    v___x_2086_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12,
    );
    v___x_2087_ = l_Nat_reprFast(v_numParams_2068_);
    v___x_2088_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
    v___x_2089_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2089_, 0, v___x_2086_);
    leanh::lean_ctor_set(v___x_2089_, 1, v___x_2088_);
    v___x_2090_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2090_, 0, v___x_2089_);
    leanh::lean_ctor_set_uint8(
        v___x_2090_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    v___x_2091_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2091_, 0, v___x_2085_);
    leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
    v___x_2092_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2092_, 0, v___x_2091_);
    leanh::lean_ctor_set(v___x_2092_, 1, v___x_2079_);
    v___x_2093_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2093_, 0, v___x_2092_);
    leanh::lean_ctor_set(v___x_2093_, 1, v___x_2081_);
    v___x_2094_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14;
    v___x_2095_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2095_, 0, v___x_2093_);
    leanh::lean_ctor_set(v___x_2095_, 1, v___x_2094_);
    v___x_2096_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2096_, 0, v___x_2095_);
    leanh::lean_ctor_set(v___x_2096_, 1, v___x_2070_);
    v___x_2097_ = l_Nat_reprFast(v_fieldIdx_2069_);
    v___x_2098_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2098_, 0, v___x_2097_);
    v___x_2099_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2099_, 0, v___x_2072_);
    leanh::lean_ctor_set(v___x_2099_, 1, v___x_2098_);
    v___x_2100_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
    leanh::lean_ctor_set_uint8(
        v___x_2100_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    v___x_2101_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2101_, 0, v___x_2096_);
    leanh::lean_ctor_set(v___x_2101_, 1, v___x_2100_);
    v___x_2102_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17,
    );
    v___x_2103_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18;
    v___x_2104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2104_, 0, v___x_2103_);
    leanh::lean_ctor_set(v___x_2104_, 1, v___x_2101_);
    v___x_2105_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19;
    v___x_2106_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2106_, 0, v___x_2104_);
    leanh::lean_ctor_set(v___x_2106_, 1, v___x_2105_);
    v___x_2107_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2107_, 0, v___x_2102_);
    leanh::lean_ctor_set(v___x_2107_, 1, v___x_2106_);
    v___x_2108_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2108_, 0, v___x_2107_);
    leanh::lean_ctor_set_uint8(
        v___x_2108_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    return v___x_2108_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr(
    mut v_x_2109_: *mut leanh::LeanObject,
    mut v_prec_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2111_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg(v_x_2109_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___boxed(
    mut v_x_2112_: *mut leanh::LeanObject,
    mut v_prec_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr(v_x_2112_, v_prec_2113_);
    leanh::lean_dec(v_prec_2113_);
    return v_res_2114_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(
    mut v_upperBound_2119_: *mut leanh::LeanObject,
    mut v_val_2120_: *mut leanh::LeanObject,
    mut v_head_2121_: *mut leanh::LeanObject,
    mut v_a_2122_: *mut leanh::LeanObject,
    mut v___x_2123_: u8,
    mut v_a_2124_: *mut leanh::LeanObject,
    mut v_b_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: u8 = 0;
    let mut v_numParams_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_unused_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2132_ = lean_nat_dec_lt(v_a_2124_, v_upperBound_2119_);
                if v___x_2132_ == 0 {
                    leanh::lean_dec(v_a_2124_);
                    leanh::lean_dec(v_head_2121_);
                    v___x_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2133_, 0, v_b_2125_);
                    return v___x_2133_;
                } else {
                    v_snd_2134_ = leanh::lean_ctor_get(v_b_2125_, 1);
                    v_isSharedCheck_2158_ = (!leanh::lean_is_exclusive(v_b_2125_)) as u8;
                    if v_isSharedCheck_2158_ == 0 {
                        v_unused_2159_ = leanh::lean_ctor_get(v_b_2125_, 0);
                        leanh::lean_dec(v_unused_2159_);
                        v___x_2136_ = v_b_2125_;
                        v_isShared_2137_ = v_isSharedCheck_2158_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2134_);
                        leanh::lean_dec(v_b_2125_);
                        v___x_2136_ = leanh::lean_box(0);
                        v_isShared_2137_ = v_isSharedCheck_2158_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2129_ = leanh::lean_unsigned_to_nat(1);
                v___x_2130_ = lean_nat_add(v_a_2124_, v___x_2129_);
                leanh::lean_dec(v_a_2124_);
                v_a_2124_ = v___x_2130_;
                v_b_2125_ = v_a_2128_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2138_ = leanh::lean_box(0);
                v___x_2139_ = lean_array_fget_borrowed(v_a_2122_, v_a_2124_);
                v___x_2140_ = (leanh::lean_unbox(v___x_2139_) as u8);
                if v___x_2140_ == 0 {
                    if v_isShared_2137_ == 0 {
                        leanh::lean_ctor_set(v___x_2136_, 0, v___x_2138_);
                        v___x_2142_ = v___x_2136_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2143_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2138_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_snd_2134_);
                        v___x_2142_ = v_reuseFailAlloc_2143_;
                        state = 3;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v_snd_2134_) == 0 {
                        v___y_2145_ = v___x_2123_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2157_ = (leanh::lean_unbox(v___x_2139_) as u8);
                        v___y_2145_ = v___x_2157_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_2128_ = v___x_2142_;
                state = 1;
                continue;
            }
            4 => {
                if v___y_2145_ == 0 {
                    leanh::lean_dec(v_snd_2134_);
                    v_numParams_2146_ = leanh::lean_ctor_get(v_val_2120_, 1);
                    leanh::lean_inc(v_a_2124_);
                    leanh::lean_inc(v_numParams_2146_);
                    leanh::lean_inc(v_head_2121_);
                    v___x_2147_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2147_, 0, v_head_2121_);
                    leanh::lean_ctor_set(v___x_2147_, 1, v_numParams_2146_);
                    leanh::lean_ctor_set(v___x_2147_, 2, v_a_2124_);
                    v___x_2148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2148_, 0, v___x_2147_);
                    if v_isShared_2137_ == 0 {
                        leanh::lean_ctor_set(v___x_2136_, 1, v___x_2148_);
                        leanh::lean_ctor_set(v___x_2136_, 0, v___x_2138_);
                        v___x_2150_ = v___x_2136_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2151_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2138_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2148_);
                        v___x_2150_ = v_reuseFailAlloc_2151_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2124_);
                    leanh::lean_dec(v_head_2121_);
                    v___x_2152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0;
                    if v_isShared_2137_ == 0 {
                        leanh::lean_ctor_set(v___x_2136_, 0, v___x_2152_);
                        v___x_2154_ = v___x_2136_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2152_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_snd_2134_);
                        v___x_2154_ = v_reuseFailAlloc_2156_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_a_2128_ = v___x_2150_;
                state = 1;
                continue;
            }
            6 => {
                v___x_2155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                return v___x_2155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___boxed(
    mut v_upperBound_2160_: *mut leanh::LeanObject,
    mut v_val_2161_: *mut leanh::LeanObject,
    mut v_head_2162_: *mut leanh::LeanObject,
    mut v_a_2163_: *mut leanh::LeanObject,
    mut v___x_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_b_2166_: *mut leanh::LeanObject,
    mut v___y_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4263__boxed_2168_: u8 = 0;
    let mut v_res_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4263__boxed_2168_ = (leanh::lean_unbox(v___x_2164_) as u8);
    v_res_2169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(v_upperBound_2160_, v_val_2161_, v_head_2162_, v_a_2163_, v___x_4263__boxed_2168_, v_a_2165_, v_b_2166_);
    leanh::lean_dec_ref(v_a_2163_);
    leanh::lean_dec_ref(v_val_2161_);
    leanh::lean_dec(v_upperBound_2160_);
    return v_res_2169_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache(
    mut v_trivialType_2172_: *mut leanh::LeanObject,
    mut v_declName_2173_: *mut leanh::LeanObject,
    mut v_a_2174_: *mut leanh::LeanObject,
    mut v_a_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_2192_: u8 = 0;
    let mut v_isRec_2193_: u8 = 0;
    let mut v_ctors_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v_fst_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut v_a_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2231_: u8 = 0;
    let mut v_a_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_a_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut v_a_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2259_: u8 = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2180_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_declName_2173_);
                if v___x_2180_ == 0 {
                    v___x_2181_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(v_declName_2173_, v_a_2174_, v_a_2175_);
                    if leanh::lean_obj_tag(v___x_2181_) == 0 {
                        v_a_2182_ = leanh::lean_ctor_get(v___x_2181_, 0);
                        v_isSharedCheck_2255_ =
                            (!leanh::lean_is_exclusive(v___x_2181_)) as u8;
                        if v_isSharedCheck_2255_ == 0 {
                            v___x_2184_ = v___x_2181_;
                            v_isShared_2185_ = v_isSharedCheck_2255_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2182_);
                            leanh::lean_dec(v___x_2181_);
                            v___x_2184_ = leanh::lean_box(0);
                            v_isShared_2185_ = v_isSharedCheck_2255_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_trivialType_2172_);
                        v_a_2256_ = leanh::lean_ctor_get(v___x_2181_, 0);
                        v_isSharedCheck_2263_ =
                            (!leanh::lean_is_exclusive(v___x_2181_)) as u8;
                        if v_isSharedCheck_2263_ == 0 {
                            v___x_2258_ = v___x_2181_;
                            v_isShared_2259_ = v_isSharedCheck_2263_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2256_);
                            leanh::lean_dec(v___x_2181_);
                            v___x_2258_ = leanh::lean_box(0);
                            v_isShared_2259_ = v_isSharedCheck_2263_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_2173_);
                    leanh::lean_dec_ref(v_trivialType_2172_);
                    v___x_2264_ = leanh::lean_box(0);
                    v___x_2265_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2265_, 0, v___x_2264_);
                    return v___x_2265_;
                }
            }
            1 => {
                v___x_2178_ = leanh::lean_box(0);
                v___x_2179_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2179_, 0, v___x_2178_);
                return v___x_2179_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2182_) == 5 {
                    v_val_2191_ = leanh::lean_ctor_get(v_a_2182_, 0);
                    leanh::lean_inc_ref(v_val_2191_);
                    leanh::lean_dec_ref_known(v_a_2182_, 1);
                    v_isUnsafe_2192_ = leanh::lean_ctor_get_uint8(
                        v_val_2191_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6 + 1) as u32,
                    );
                    if v_isUnsafe_2192_ == 0 {
                        v_isRec_2193_ = leanh::lean_ctor_get_uint8(
                            v_val_2191_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        );
                        if v_isRec_2193_ == 0 {
                            leanh::lean_del_object(v___x_2184_);
                            v_ctors_2194_ = leanh::lean_ctor_get(v_val_2191_, 4);
                            if leanh::lean_obj_tag(v_ctors_2194_) == 1 {
                                v_tail_2195_ = leanh::lean_ctor_get(v_ctors_2194_, 1);
                                if leanh::lean_obj_tag(v_tail_2195_) == 0 {
                                    v_head_2196_ = leanh::lean_ctor_get(v_ctors_2194_, 0);
                                    leanh::lean_inc_n(v_head_2196_, 2);
                                    v___x_2197_ = leanh::lean_box(0);
                                    v___x_2198_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                                        v_head_2196_,
                                        v___x_2197_,
                                        v_a_2174_,
                                        v_a_2175_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2198_) == 0 {
                                        v_a_2199_ = leanh::lean_ctor_get(v___x_2198_, 0);
                                        v_isSharedCheck_2244_ =
                                            (!leanh::lean_is_exclusive(v___x_2198_)) as u8;
                                        if v_isSharedCheck_2244_ == 0 {
                                            v___x_2201_ = v___x_2198_;
                                            v_isShared_2202_ = v_isSharedCheck_2244_;
                                            state = 5;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2199_);
                                            leanh::lean_dec(v___x_2198_);
                                            v___x_2201_ = leanh::lean_box(0);
                                            v_isShared_2202_ = v_isSharedCheck_2244_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_head_2196_);
                                        leanh::lean_dec_ref(v_val_2191_);
                                        leanh::lean_dec_ref(v_trivialType_2172_);
                                        v_a_2245_ = leanh::lean_ctor_get(v___x_2198_, 0);
                                        v_isSharedCheck_2252_ =
                                            (!leanh::lean_is_exclusive(v___x_2198_)) as u8;
                                        if v_isSharedCheck_2252_ == 0 {
                                            v___x_2247_ = v___x_2198_;
                                            v_isShared_2248_ = v_isSharedCheck_2252_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2245_);
                                            leanh::lean_dec(v___x_2198_);
                                            v___x_2247_ = leanh::lean_box(0);
                                            v_isShared_2248_ = v_isSharedCheck_2252_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_val_2191_);
                                    leanh::lean_dec_ref(v_trivialType_2172_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_val_2191_);
                                leanh::lean_dec_ref(v_trivialType_2172_);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_val_2191_);
                            leanh::lean_dec_ref(v_trivialType_2172_);
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_val_2191_);
                        leanh::lean_dec_ref(v_trivialType_2172_);
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2184_);
                    leanh::lean_dec(v_a_2182_);
                    leanh::lean_dec_ref(v_trivialType_2172_);
                    v___x_2253_ = leanh::lean_box(0);
                    v___x_2254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
                    return v___x_2254_;
                }
            }
            3 => {
                v___x_2187_ = leanh::lean_box(0);
                if v_isShared_2185_ == 0 {
                    leanh::lean_ctor_set(v___x_2184_, 0, v___x_2187_);
                    v___x_2189_ = v___x_2184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
                    v___x_2189_ = v_reuseFailAlloc_2190_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2189_;
            }
            5 => {
                v___x_2203_ = l_Lean_Expr_isErased(v_a_2199_);
                leanh::lean_dec(v_a_2199_);
                if v___x_2203_ == 0 {
                    leanh::lean_del_object(v___x_2201_);
                    leanh::lean_inc(v_head_2196_);
                    v___x_2204_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields(v_head_2196_, v_trivialType_2172_, v_a_2174_, v_a_2175_);
                    if leanh::lean_obj_tag(v___x_2204_) == 0 {
                        v_a_2205_ = leanh::lean_ctor_get(v___x_2204_, 0);
                        leanh::lean_inc(v_a_2205_);
                        leanh::lean_dec_ref_known(v___x_2204_, 1);
                        v___x_2206_ = lean_array_get_size(v_a_2205_);
                        v___x_2207_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2208_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0;
                        v___x_2209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(v___x_2206_, v_val_2191_, v_head_2196_, v_a_2205_, v___x_2203_, v___x_2207_, v___x_2208_);
                        leanh::lean_dec(v_a_2205_);
                        leanh::lean_dec_ref(v_val_2191_);
                        if leanh::lean_obj_tag(v___x_2209_) == 0 {
                            v_a_2210_ = leanh::lean_ctor_get(v___x_2209_, 0);
                            v_isSharedCheck_2223_ =
                                (!leanh::lean_is_exclusive(v___x_2209_)) as u8;
                            if v_isSharedCheck_2223_ == 0 {
                                v___x_2212_ = v___x_2209_;
                                v_isShared_2213_ = v_isSharedCheck_2223_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2210_);
                                leanh::lean_dec(v___x_2209_);
                                v___x_2212_ = leanh::lean_box(0);
                                v_isShared_2213_ = v_isSharedCheck_2223_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_2224_ = leanh::lean_ctor_get(v___x_2209_, 0);
                            v_isSharedCheck_2231_ =
                                (!leanh::lean_is_exclusive(v___x_2209_)) as u8;
                            if v_isSharedCheck_2231_ == 0 {
                                v___x_2226_ = v___x_2209_;
                                v_isShared_2227_ = v_isSharedCheck_2231_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2224_);
                                leanh::lean_dec(v___x_2209_);
                                v___x_2226_ = leanh::lean_box(0);
                                v_isShared_2227_ = v_isSharedCheck_2231_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_head_2196_);
                        leanh::lean_dec_ref(v_val_2191_);
                        v_a_2232_ = leanh::lean_ctor_get(v___x_2204_, 0);
                        v_isSharedCheck_2239_ =
                            (!leanh::lean_is_exclusive(v___x_2204_)) as u8;
                        if v_isSharedCheck_2239_ == 0 {
                            v___x_2234_ = v___x_2204_;
                            v_isShared_2235_ = v_isSharedCheck_2239_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2232_);
                            leanh::lean_dec(v___x_2204_);
                            v___x_2234_ = leanh::lean_box(0);
                            v_isShared_2235_ = v_isSharedCheck_2239_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_head_2196_);
                    leanh::lean_dec_ref(v_val_2191_);
                    leanh::lean_dec_ref(v_trivialType_2172_);
                    v___x_2240_ = leanh::lean_box(0);
                    if v_isShared_2202_ == 0 {
                        leanh::lean_ctor_set(v___x_2201_, 0, v___x_2240_);
                        v___x_2242_ = v___x_2201_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
                        v___x_2242_ = v_reuseFailAlloc_2243_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_2214_ = leanh::lean_ctor_get(v_a_2210_, 0);
                if leanh::lean_obj_tag(v_fst_2214_) == 0 {
                    v_snd_2215_ = leanh::lean_ctor_get(v_a_2210_, 1);
                    leanh::lean_inc(v_snd_2215_);
                    leanh::lean_dec(v_a_2210_);
                    if v_isShared_2213_ == 0 {
                        leanh::lean_ctor_set(v___x_2212_, 0, v_snd_2215_);
                        v___x_2217_ = v___x_2212_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2218_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_snd_2215_);
                        v___x_2217_ = v_reuseFailAlloc_2218_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2214_);
                    leanh::lean_dec(v_a_2210_);
                    v_val_2219_ = leanh::lean_ctor_get(v_fst_2214_, 0);
                    leanh::lean_inc(v_val_2219_);
                    leanh::lean_dec_ref_known(v_fst_2214_, 1);
                    if v_isShared_2213_ == 0 {
                        leanh::lean_ctor_set(v___x_2212_, 0, v_val_2219_);
                        v___x_2221_ = v___x_2212_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_val_2219_);
                        v___x_2221_ = v_reuseFailAlloc_2222_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2217_;
            }
            8 => {
                return v___x_2221_;
            }
            9 => {
                if v_isShared_2227_ == 0 {
                    v___x_2229_ = v___x_2226_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
                    v___x_2229_ = v_reuseFailAlloc_2230_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2229_;
            }
            11 => {
                if v_isShared_2235_ == 0 {
                    v___x_2237_ = v___x_2234_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
                    v___x_2237_ = v_reuseFailAlloc_2238_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2237_;
            }
            13 => {
                return v___x_2242_;
            }
            14 => {
                if v_isShared_2248_ == 0 {
                    v___x_2250_ = v___x_2247_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
                    v___x_2250_ = v_reuseFailAlloc_2251_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2250_;
            }
            16 => {
                if v_isShared_2259_ == 0 {
                    v___x_2261_ = v___x_2258_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
                    v___x_2261_ = v_reuseFailAlloc_2262_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___boxed(
    mut v_trivialType_2266_: *mut leanh::LeanObject,
    mut v_declName_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
    mut v_a_2269_: *mut leanh::LeanObject,
    mut v_a_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache(v_trivialType_2266_, v_declName_2267_, v_a_2268_, v_a_2269_);
    leanh::lean_dec(v_a_2269_);
    leanh::lean_dec_ref(v_a_2268_);
    return v_res_2271_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0(
    mut v_upperBound_2272_: *mut leanh::LeanObject,
    mut v_val_2273_: *mut leanh::LeanObject,
    mut v_head_2274_: *mut leanh::LeanObject,
    mut v_a_2275_: *mut leanh::LeanObject,
    mut v___x_2276_: u8,
    mut v_inst_2277_: *mut leanh::LeanObject,
    mut v_R_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_b_2280_: *mut leanh::LeanObject,
    mut v_c_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(v_upperBound_2272_, v_val_2273_, v_head_2274_, v_a_2275_, v___x_2276_, v_a_2279_, v_b_2280_);
    return v___x_2285_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___boxed(
    mut v_upperBound_2286_: *mut leanh::LeanObject,
    mut v_val_2287_: *mut leanh::LeanObject,
    mut v_head_2288_: *mut leanh::LeanObject,
    mut v_a_2289_: *mut leanh::LeanObject,
    mut v___x_2290_: *mut leanh::LeanObject,
    mut v_inst_2291_: *mut leanh::LeanObject,
    mut v_R_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_b_2294_: *mut leanh::LeanObject,
    mut v_c_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4525__boxed_2299_: u8 = 0;
    let mut v_res_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4525__boxed_2299_ = (leanh::lean_unbox(v___x_2290_) as u8);
    v_res_2300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0(v_upperBound_2286_, v_val_2287_, v_head_2288_, v_a_2289_, v___x_4525__boxed_2299_, v_inst_2291_, v_R_2292_, v_a_2293_, v_b_2294_, v_c_2295_, v___y_2296_, v___y_2297_);
    leanh::lean_dec(v___y_2297_);
    leanh::lean_dec_ref(v___y_2296_);
    leanh::lean_dec_ref(v_a_2289_);
    leanh::lean_dec_ref(v_val_2287_);
    leanh::lean_dec(v_upperBound_2286_);
    return v_res_2300_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(
    mut v_x_2301_: *mut leanh::LeanObject,
    mut v_x_2302_: *mut leanh::LeanObject,
    mut v_x_2303_: *mut leanh::LeanObject,
    mut v_x_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: u8 = 0;
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2305_ = leanh::lean_ctor_get(v_x_2301_, 0);
                v_vs_2306_ = leanh::lean_ctor_get(v_x_2301_, 1);
                v_isSharedCheck_2330_ = (!leanh::lean_is_exclusive(v_x_2301_)) as u8;
                if v_isSharedCheck_2330_ == 0 {
                    v___x_2308_ = v_x_2301_;
                    v_isShared_2309_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2306_);
                    leanh::lean_inc(v_ks_2305_);
                    leanh::lean_dec(v_x_2301_);
                    v___x_2308_ = leanh::lean_box(0);
                    v_isShared_2309_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2310_ = lean_array_get_size(v_ks_2305_);
                v___x_2311_ = lean_nat_dec_lt(v_x_2302_, v___x_2310_);
                if v___x_2311_ == 0 {
                    leanh::lean_dec(v_x_2302_);
                    v___x_2312_ = lean_array_push(v_ks_2305_, v_x_2303_);
                    v___x_2313_ = lean_array_push(v_vs_2306_, v_x_2304_);
                    if v_isShared_2309_ == 0 {
                        leanh::lean_ctor_set(v___x_2308_, 1, v___x_2313_);
                        leanh::lean_ctor_set(v___x_2308_, 0, v___x_2312_);
                        v___x_2315_ = v___x_2308_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2316_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2313_);
                        v___x_2315_ = v_reuseFailAlloc_2316_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2317_ = lean_array_fget_borrowed(v_ks_2305_, v_x_2302_);
                    v___x_2318_ = lean_name_eq(v_x_2303_, v_k_x27_2317_);
                    if v___x_2318_ == 0 {
                        if v_isShared_2309_ == 0 {
                            v___x_2320_ = v___x_2308_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2324_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_ks_2305_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_vs_2306_);
                            v___x_2320_ = v_reuseFailAlloc_2324_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2325_ = lean_array_fset(v_ks_2305_, v_x_2302_, v_x_2303_);
                        v___x_2326_ = lean_array_fset(v_vs_2306_, v_x_2302_, v_x_2304_);
                        leanh::lean_dec(v_x_2302_);
                        if v_isShared_2309_ == 0 {
                            leanh::lean_ctor_set(v___x_2308_, 1, v___x_2326_);
                            leanh::lean_ctor_set(v___x_2308_, 0, v___x_2325_);
                            v___x_2328_ = v___x_2308_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2329_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2325_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2326_);
                            v___x_2328_ = v_reuseFailAlloc_2329_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2315_;
            }
            3 => {
                v___x_2321_ = leanh::lean_unsigned_to_nat(1);
                v___x_2322_ = lean_nat_add(v_x_2302_, v___x_2321_);
                leanh::lean_dec(v_x_2302_);
                v_x_2301_ = v___x_2320_;
                v_x_2302_ = v___x_2322_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_n_2331_: *mut leanh::LeanObject,
    mut v_k_2332_: *mut leanh::LeanObject,
    mut v_v_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = leanh::lean_unsigned_to_nat(0);
    v___x_2335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_n_2331_, v___x_2334_, v_k_2332_, v_v_2333_);
    return v___x_2335_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: u64 = 0;
    v___x_2336_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2337_ = lean_uint64_of_nat(v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_2338_: usize = 0;
    let mut v___x_2339_: usize = 0;
    let mut v___x_2340_: usize = 0;
    v___x_2338_ = 5usize;
    v___x_2339_ = 1usize;
    v___x_2340_ = lean_usize_shift_left(v___x_2339_, v___x_2338_);
    return v___x_2340_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_2341_: usize = 0;
    let mut v___x_2342_: usize = 0;
    let mut v___x_2343_: usize = 0;
    v___x_2341_ = 1usize;
    v___x_2342_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0);
    v___x_2343_ = lean_usize_sub(v___x_2342_, v___x_2341_);
    return v___x_2343_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2344_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_x_2345_: *mut leanh::LeanObject,
    mut v_x_2346_: usize,
    mut v_x_2347_: usize,
    mut v_x_2348_: *mut leanh::LeanObject,
    mut v_x_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    let mut v_j_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v_v_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_node_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v___x_2386_: usize = 0;
    let mut v___x_2387_: usize = 0;
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_unused_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: u8 = 0;
    let mut v_ks_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: usize = 0;
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: u8 = 0;
    let mut v_reuseFailAlloc_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2345_) == 0 {
                    v_es_2350_ = leanh::lean_ctor_get(v_x_2345_, 0);
                    v___x_2351_ = 5usize;
                    v___x_2352_ = 1usize;
                    v___x_2353_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_2354_ = lean_usize_land(v_x_2346_, v___x_2353_);
                    v_j_2355_ = lean_usize_to_nat(v___x_2354_);
                    v___x_2356_ = lean_array_get_size(v_es_2350_);
                    v___x_2357_ = lean_nat_dec_lt(v_j_2355_, v___x_2356_);
                    if v___x_2357_ == 0 {
                        leanh::lean_dec(v_j_2355_);
                        leanh::lean_dec(v_x_2349_);
                        leanh::lean_dec(v_x_2348_);
                        return v_x_2345_;
                    } else {
                        leanh::lean_inc_ref(v_es_2350_);
                        v_isSharedCheck_2394_ = (!leanh::lean_is_exclusive(v_x_2345_)) as u8;
                        if v_isSharedCheck_2394_ == 0 {
                            v_unused_2395_ = leanh::lean_ctor_get(v_x_2345_, 0);
                            leanh::lean_dec(v_unused_2395_);
                            v___x_2359_ = v_x_2345_;
                            v_isShared_2360_ = v_isSharedCheck_2394_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2345_);
                            v___x_2359_ = leanh::lean_box(0);
                            v_isShared_2360_ = v_isSharedCheck_2394_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2396_ = leanh::lean_ctor_get(v_x_2345_, 0);
                    v_vs_2397_ = leanh::lean_ctor_get(v_x_2345_, 1);
                    v_isSharedCheck_2417_ = (!leanh::lean_is_exclusive(v_x_2345_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2399_ = v_x_2345_;
                        v_isShared_2400_ = v_isSharedCheck_2417_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2397_);
                        leanh::lean_inc(v_ks_2396_);
                        leanh::lean_dec(v_x_2345_);
                        v___x_2399_ = leanh::lean_box(0);
                        v_isShared_2400_ = v_isSharedCheck_2417_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2361_ = lean_array_fget(v_es_2350_, v_j_2355_);
                v___x_2362_ = leanh::lean_box(0);
                v_xs_x27_2363_ = lean_array_fset(v_es_2350_, v_j_2355_, v___x_2362_);
                match leanh::lean_obj_tag(v_v_2361_) {
                    0 => {
                        v_key_2370_ = leanh::lean_ctor_get(v_v_2361_, 0);
                        v_val_2371_ = leanh::lean_ctor_get(v_v_2361_, 1);
                        v_isSharedCheck_2381_ = (!leanh::lean_is_exclusive(v_v_2361_)) as u8;
                        if v_isSharedCheck_2381_ == 0 {
                            v___x_2373_ = v_v_2361_;
                            v_isShared_2374_ = v_isSharedCheck_2381_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2371_);
                            leanh::lean_inc(v_key_2370_);
                            leanh::lean_dec(v_v_2361_);
                            v___x_2373_ = leanh::lean_box(0);
                            v_isShared_2374_ = v_isSharedCheck_2381_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2382_ = leanh::lean_ctor_get(v_v_2361_, 0);
                        v_isSharedCheck_2392_ = (!leanh::lean_is_exclusive(v_v_2361_)) as u8;
                        if v_isSharedCheck_2392_ == 0 {
                            v___x_2384_ = v_v_2361_;
                            v_isShared_2385_ = v_isSharedCheck_2392_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2382_);
                            leanh::lean_dec(v_v_2361_);
                            v___x_2384_ = leanh::lean_box(0);
                            v_isShared_2385_ = v_isSharedCheck_2392_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2393_, 0, v_x_2348_);
                        leanh::lean_ctor_set(v___x_2393_, 1, v_x_2349_);
                        v___y_2365_ = v___x_2393_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2366_ = lean_array_fset(v_xs_x27_2363_, v_j_2355_, v___y_2365_);
                leanh::lean_dec(v_j_2355_);
                if v_isShared_2360_ == 0 {
                    leanh::lean_ctor_set(v___x_2359_, 0, v___x_2366_);
                    v___x_2368_ = v___x_2359_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
                    v___x_2368_ = v_reuseFailAlloc_2369_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2368_;
            }
            4 => {
                v___x_2375_ = lean_name_eq(v_x_2348_, v_key_2370_);
                if v___x_2375_ == 0 {
                    leanh::lean_del_object(v___x_2373_);
                    v___x_2376_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2370_,
                        v_val_2371_,
                        v_x_2348_,
                        v_x_2349_,
                    );
                    v___x_2377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2377_, 0, v___x_2376_);
                    v___y_2365_ = v___x_2377_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2371_);
                    leanh::lean_dec(v_key_2370_);
                    if v_isShared_2374_ == 0 {
                        leanh::lean_ctor_set(v___x_2373_, 1, v_x_2349_);
                        leanh::lean_ctor_set(v___x_2373_, 0, v_x_2348_);
                        v___x_2379_ = v___x_2373_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_x_2348_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_x_2349_);
                        v___x_2379_ = v_reuseFailAlloc_2380_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2365_ = v___x_2379_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2386_ = lean_usize_shift_right(v_x_2346_, v___x_2351_);
                v___x_2387_ = lean_usize_add(v_x_2347_, v___x_2352_);
                v___x_2388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_node_2382_, v___x_2386_, v___x_2387_, v_x_2348_, v_x_2349_);
                if v_isShared_2385_ == 0 {
                    leanh::lean_ctor_set(v___x_2384_, 0, v___x_2388_);
                    v___x_2390_ = v___x_2384_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
                    v___x_2390_ = v_reuseFailAlloc_2391_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2365_ = v___x_2390_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2400_ == 0 {
                    v___x_2402_ = v___x_2399_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_ks_2396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_vs_2397_);
                    v___x_2402_ = v_reuseFailAlloc_2416_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2403_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2402_, v_x_2348_, v_x_2349_);
                v___x_2411_ = 7usize;
                v___x_2412_ = lean_usize_dec_le(v___x_2411_, v_x_2347_);
                if v___x_2412_ == 0 {
                    v___x_2413_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2403_);
                    v___x_2414_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
                    leanh::lean_dec(v___x_2413_);
                    v___y_2405_ = v___x_2415_;
                    state = 10;
                    continue;
                } else {
                    v___y_2405_ = v___x_2412_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2405_ == 0 {
                    v_ks_2406_ = leanh::lean_ctor_get(v_newNode_2403_, 0);
                    leanh::lean_inc_ref(v_ks_2406_);
                    v_vs_2407_ = leanh::lean_ctor_get(v_newNode_2403_, 1);
                    leanh::lean_inc_ref(v_vs_2407_);
                    leanh::lean_dec_ref(v_newNode_2403_);
                    v___x_2408_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2409_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2);
                    v___x_2410_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(v_x_2347_, v_ks_2406_, v_vs_2407_, v___x_2408_, v___x_2409_);
                    leanh::lean_dec_ref(v_vs_2407_);
                    leanh::lean_dec_ref(v_ks_2406_);
                    return v___x_2410_;
                } else {
                    return v_newNode_2403_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_depth_2418_: usize,
    mut v_keys_2419_: *mut leanh::LeanObject,
    mut v_vals_2420_: *mut leanh::LeanObject,
    mut v_i_2421_: *mut leanh::LeanObject,
    mut v_entries_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v_k_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: u64 = 0;
    let mut v_h_2429_: usize = 0;
    let mut v___x_2430_: usize = 0;
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: usize = 0;
    let mut v___x_2433_: usize = 0;
    let mut v___x_2434_: usize = 0;
    let mut v_h_2435_: usize = 0;
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u64 = 0;
    let mut v_hash_2440_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2423_ = lean_array_get_size(v_keys_2419_);
                v___x_2424_ = lean_nat_dec_lt(v_i_2421_, v___x_2423_);
                if v___x_2424_ == 0 {
                    leanh::lean_dec(v_i_2421_);
                    return v_entries_2422_;
                } else {
                    v_k_2425_ = lean_array_fget_borrowed(v_keys_2419_, v_i_2421_);
                    v_v_2426_ = lean_array_fget_borrowed(v_vals_2420_, v_i_2421_);
                    if leanh::lean_obj_tag(v_k_2425_) == 0 {
                        v___x_2439_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
                        v___y_2428_ = v___x_2439_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2440_ = leanh::lean_ctor_get_uint64(
                            v_k_2425_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2428_ = v_hash_2440_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2429_ = lean_uint64_to_usize(v___y_2428_);
                v___x_2430_ = 5usize;
                v___x_2431_ = leanh::lean_unsigned_to_nat(1);
                v___x_2432_ = 1usize;
                v___x_2433_ = lean_usize_sub(v_depth_2418_, v___x_2432_);
                v___x_2434_ = lean_usize_mul(v___x_2430_, v___x_2433_);
                v_h_2435_ = lean_usize_shift_right(v_h_2429_, v___x_2434_);
                v___x_2436_ = lean_nat_add(v_i_2421_, v___x_2431_);
                leanh::lean_dec(v_i_2421_);
                leanh::lean_inc(v_v_2426_);
                leanh::lean_inc(v_k_2425_);
                v___x_2437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_entries_2422_, v_h_2435_, v_depth_2418_, v_k_2425_, v_v_2426_);
                v_i_2421_ = v___x_2436_;
                v_entries_2422_ = v___x_2437_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_depth_2441_: *mut leanh::LeanObject,
    mut v_keys_2442_: *mut leanh::LeanObject,
    mut v_vals_2443_: *mut leanh::LeanObject,
    mut v_i_2444_: *mut leanh::LeanObject,
    mut v_entries_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2446_: usize = 0;
    let mut v_res_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2446_ = leanh::lean_unbox_usize(v_depth_2441_);
    leanh::lean_dec(v_depth_2441_);
    v_res_2447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(v_depth_boxed_2446_, v_keys_2442_, v_vals_2443_, v_i_2444_, v_entries_2445_);
    leanh::lean_dec_ref(v_vals_2443_);
    leanh::lean_dec_ref(v_keys_2442_);
    return v_res_2447_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_x_2448_: *mut leanh::LeanObject,
    mut v_x_2449_: *mut leanh::LeanObject,
    mut v_x_2450_: *mut leanh::LeanObject,
    mut v_x_2451_: *mut leanh::LeanObject,
    mut v_x_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_987__boxed_2453_: usize = 0;
    let mut v_x_988__boxed_2454_: usize = 0;
    let mut v_res_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_987__boxed_2453_ = leanh::lean_unbox_usize(v_x_2449_);
    leanh::lean_dec(v_x_2449_);
    v_x_988__boxed_2454_ = leanh::lean_unbox_usize(v_x_2450_);
    leanh::lean_dec(v_x_2450_);
    v_res_2455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_x_2448_, v_x_987__boxed_2453_, v_x_988__boxed_2454_, v_x_2451_, v_x_2452_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2___redArg(
    mut v_x_2456_: *mut leanh::LeanObject,
    mut v_x_2457_: *mut leanh::LeanObject,
    mut v_x_2458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2460_: u64 = 0;
    let mut v___x_2461_: usize = 0;
    let mut v___x_2462_: usize = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u64 = 0;
    let mut v_hash_2465_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2457_) == 0 {
                    v___x_2464_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
                    v___y_2460_ = v___x_2464_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2465_ = leanh::lean_ctor_get_uint64(
                        v_x_2457_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2460_ = v_hash_2465_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2461_ = lean_uint64_to_usize(v___y_2460_);
                v___x_2462_ = 1usize;
                v___x_2463_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_x_2456_, v___x_2461_, v___x_2462_, v_x_2457_, v_x_2458_);
                return v___x_2463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___lam__0(
    mut v_a_2466_: *mut leanh::LeanObject,
    mut v_b_2467_: *mut leanh::LeanObject,
    mut v_x_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2469_ = leanh::lean_ctor_get(v_x_2468_, 0);
                v_snd_2470_ = leanh::lean_ctor_get(v_x_2468_, 1);
                v_isSharedCheck_2479_ = (!leanh::lean_is_exclusive(v_x_2468_)) as u8;
                if v_isSharedCheck_2479_ == 0 {
                    v___x_2472_ = v_x_2468_;
                    v_isShared_2473_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2470_);
                    leanh::lean_inc(v_fst_2469_);
                    leanh::lean_dec(v_x_2468_);
                    v___x_2472_ = leanh::lean_box(0);
                    v_isShared_2473_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_2466_);
                v___x_2474_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2474_, 0, v_a_2466_);
                leanh::lean_ctor_set(v___x_2474_, 1, v_fst_2469_);
                v___x_2475_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2___redArg(v_snd_2470_, v_a_2466_, v_b_2467_);
                if v_isShared_2473_ == 0 {
                    leanh::lean_ctor_set(v___x_2472_, 1, v___x_2475_);
                    leanh::lean_ctor_set(v___x_2472_, 0, v___x_2474_);
                    v___x_2477_ = v___x_2472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2475_);
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0);
    v___x_2482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2482_, 0, v___x_2481_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1);
    v___x_2484_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    leanh::lean_ctor_set(v___x_2484_, 1, v___x_2483_);
    return v___x_2484_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(
    mut v_ext_2485_: *mut leanh::LeanObject,
    mut v_a_2486_: *mut leanh::LeanObject,
    mut v_b_2487_: *mut leanh::LeanObject,
    mut v_a_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v_asyncMode_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut v_unused_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2490_ = lean_st_ref_take(v_a_2488_);
                v_env_2491_ = leanh::lean_ctor_get(v___x_2490_, 0);
                v_nextMacroScope_2492_ = leanh::lean_ctor_get(v___x_2490_, 1);
                v_ngen_2493_ = leanh::lean_ctor_get(v___x_2490_, 2);
                v_auxDeclNGen_2494_ = leanh::lean_ctor_get(v___x_2490_, 3);
                v_traceState_2495_ = leanh::lean_ctor_get(v___x_2490_, 4);
                v_messages_2496_ = leanh::lean_ctor_get(v___x_2490_, 6);
                v_infoState_2497_ = leanh::lean_ctor_get(v___x_2490_, 7);
                v_snapshotTasks_2498_ = leanh::lean_ctor_get(v___x_2490_, 8);
                v_isSharedCheck_2513_ = (!leanh::lean_is_exclusive(v___x_2490_)) as u8;
                if v_isSharedCheck_2513_ == 0 {
                    v_unused_2514_ = leanh::lean_ctor_get(v___x_2490_, 5);
                    leanh::lean_dec(v_unused_2514_);
                    v___x_2500_ = v___x_2490_;
                    v_isShared_2501_ = v_isSharedCheck_2513_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2498_);
                    leanh::lean_inc(v_infoState_2497_);
                    leanh::lean_inc(v_messages_2496_);
                    leanh::lean_inc(v_traceState_2495_);
                    leanh::lean_inc(v_auxDeclNGen_2494_);
                    leanh::lean_inc(v_ngen_2493_);
                    leanh::lean_inc(v_nextMacroScope_2492_);
                    leanh::lean_inc(v_env_2491_);
                    leanh::lean_dec(v___x_2490_);
                    v___x_2500_ = leanh::lean_box(0);
                    v_isShared_2501_ = v_isSharedCheck_2513_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_2502_ = leanh::lean_ctor_get(v_ext_2485_, 2);
                leanh::lean_inc(v_asyncMode_2502_);
                v___f_2503_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_2503_, 0, v_a_2486_);
                leanh::lean_closure_set(v___f_2503_, 1, v_b_2487_);
                v___x_2504_ = leanh::lean_box(0);
                v___x_2505_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_2485_,
                    v_env_2491_,
                    v___f_2503_,
                    v_asyncMode_2502_,
                    v___x_2504_,
                );
                leanh::lean_dec(v_asyncMode_2502_);
                v___x_2506_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2);
                if v_isShared_2501_ == 0 {
                    leanh::lean_ctor_set(v___x_2500_, 5, v___x_2506_);
                    leanh::lean_ctor_set(v___x_2500_, 0, v___x_2505_);
                    v___x_2508_ = v___x_2500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_nextMacroScope_2492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_ngen_2493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_auxDeclNGen_2494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_traceState_2495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 5, v___x_2506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_messages_2496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 7, v_infoState_2497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 8, v_snapshotTasks_2498_);
                    v___x_2508_ = v_reuseFailAlloc_2512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2509_ = lean_st_ref_set(v_a_2488_, v___x_2508_);
                v___x_2510_ = leanh::lean_box(0);
                v___x_2511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___boxed(
    mut v_ext_2515_: *mut leanh::LeanObject,
    mut v_a_2516_: *mut leanh::LeanObject,
    mut v_b_2517_: *mut leanh::LeanObject,
    mut v_a_2518_: *mut leanh::LeanObject,
    mut v_a_2519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2520_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(v_ext_2515_, v_a_2516_, v_b_2517_, v_a_2518_);
    leanh::lean_dec(v_a_2518_);
    return v_res_2520_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_2521_: *mut leanh::LeanObject,
    mut v_vals_2522_: *mut leanh::LeanObject,
    mut v_i_2523_: *mut leanh::LeanObject,
    mut v_k_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2525_ = lean_array_get_size(v_keys_2521_);
                v___x_2526_ = lean_nat_dec_lt(v_i_2523_, v___x_2525_);
                if v___x_2526_ == 0 {
                    leanh::lean_dec(v_i_2523_);
                    v___x_2527_ = leanh::lean_box(0);
                    return v___x_2527_;
                } else {
                    v_k_x27_2528_ = lean_array_fget_borrowed(v_keys_2521_, v_i_2523_);
                    v___x_2529_ = lean_name_eq(v_k_2524_, v_k_x27_2528_);
                    if v___x_2529_ == 0 {
                        v___x_2530_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2531_ = lean_nat_add(v_i_2523_, v___x_2530_);
                        leanh::lean_dec(v_i_2523_);
                        v_i_2523_ = v___x_2531_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2533_ = lean_array_fget_borrowed(v_vals_2522_, v_i_2523_);
                        leanh::lean_dec(v_i_2523_);
                        leanh::lean_inc(v___x_2533_);
                        v___x_2534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2534_, 0, v___x_2533_);
                        return v___x_2534_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_2535_: *mut leanh::LeanObject,
    mut v_vals_2536_: *mut leanh::LeanObject,
    mut v_i_2537_: *mut leanh::LeanObject,
    mut v_k_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2535_, v_vals_2536_, v_i_2537_, v_k_2538_);
    leanh::lean_dec(v_k_2538_);
    leanh::lean_dec_ref(v_vals_2536_);
    leanh::lean_dec_ref(v_keys_2535_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_2540_: *mut leanh::LeanObject,
    mut v_x_2541_: usize,
    mut v_x_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: usize = 0;
    let mut v___x_2546_: usize = 0;
    let mut v___x_2547_: usize = 0;
    let mut v_j_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2540_) == 0 {
                    v_es_2543_ = leanh::lean_ctor_get(v_x_2540_, 0);
                    v___x_2544_ = leanh::lean_box(2);
                    v___x_2545_ = 5usize;
                    v___x_2546_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_2547_ = lean_usize_land(v_x_2541_, v___x_2546_);
                    v_j_2548_ = lean_usize_to_nat(v___x_2547_);
                    v___x_2549_ = lean_array_get_borrowed(v___x_2544_, v_es_2543_, v_j_2548_);
                    leanh::lean_dec(v_j_2548_);
                    match leanh::lean_obj_tag(v___x_2549_) {
                        0 => {
                            v_key_2550_ = leanh::lean_ctor_get(v___x_2549_, 0);
                            v_val_2551_ = leanh::lean_ctor_get(v___x_2549_, 1);
                            v___x_2552_ = lean_name_eq(v_x_2542_, v_key_2550_);
                            if v___x_2552_ == 0 {
                                v___x_2553_ = leanh::lean_box(0);
                                return v___x_2553_;
                            } else {
                                leanh::lean_inc(v_val_2551_);
                                v___x_2554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2554_, 0, v_val_2551_);
                                return v___x_2554_;
                            }
                        }
                        1 => {
                            v_node_2555_ = leanh::lean_ctor_get(v___x_2549_, 0);
                            v___x_2556_ = lean_usize_shift_right(v_x_2541_, v___x_2545_);
                            v_x_2540_ = v_node_2555_;
                            v_x_2541_ = v___x_2556_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2558_ = leanh::lean_box(0);
                            return v___x_2558_;
                        }
                    }
                } else {
                    v_ks_2559_ = leanh::lean_ctor_get(v_x_2540_, 0);
                    v_vs_2560_ = leanh::lean_ctor_get(v_x_2540_, 1);
                    v___x_2561_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2562_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2559_, v_vs_2560_, v___x_2561_, v_x_2542_);
                    return v___x_2562_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2563_: *mut leanh::LeanObject,
    mut v_x_2564_: *mut leanh::LeanObject,
    mut v_x_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1274__boxed_2566_: usize = 0;
    let mut v_res_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1274__boxed_2566_ = leanh::lean_unbox_usize(v_x_2564_);
    leanh::lean_dec(v_x_2564_);
    v_res_2567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(v_x_2563_, v_x_1274__boxed_2566_, v_x_2565_);
    leanh::lean_dec(v_x_2565_);
    leanh::lean_dec_ref(v_x_2563_);
    return v_res_2567_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(
    mut v_x_2568_: *mut leanh::LeanObject,
    mut v_x_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2571_: u64 = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u64 = 0;
    let mut v_hash_2575_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2569_) == 0 {
                    v___x_2574_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
                    v___y_2571_ = v___x_2574_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2575_ = leanh::lean_ctor_get_uint64(
                        v_x_2569_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2571_ = v_hash_2575_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2572_ = lean_uint64_to_usize(v___y_2571_);
                v___x_2573_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(v_x_2568_, v___x_2572_, v_x_2569_);
                return v___x_2573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2576_: *mut leanh::LeanObject,
    mut v_x_2577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2578_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(v_x_2576_, v_x_2577_);
    leanh::lean_dec(v_x_2577_);
    leanh::lean_dec_ref(v_x_2576_);
    return v_res_2578_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2581_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1;
    v___x_2582_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0;
    v___x_2583_ = l_Lean_PersistentHashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2582_,
        v___x_2581_,
    );
    return v___x_2583_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2);
    v___x_2585_ = leanh::lean_box(0);
    v___x_2586_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2586_, 0, v___x_2585_);
    leanh::lean_ctor_set(v___x_2586_, 1, v___x_2584_);
    return v___x_2586_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(
    mut v_ext_2587_: *mut leanh::LeanObject,
    mut v_a_2588_: *mut leanh::LeanObject,
    mut v_a_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = lean_st_ref_get(v_a_2589_);
    v_env_2592_ = leanh::lean_ctor_get(v___x_2591_, 0);
    leanh::lean_inc_ref(v_env_2592_);
    leanh::lean_dec(v___x_2591_);
    v_asyncMode_2593_ = leanh::lean_ctor_get(v_ext_2587_, 2);
    v___x_2594_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3);
    v___x_2595_ = leanh::lean_box(0);
    v___x_2596_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_2594_,
        v_ext_2587_,
        v_env_2592_,
        v_asyncMode_2593_,
        v___x_2595_,
    );
    v_snd_2597_ = leanh::lean_ctor_get(v___x_2596_, 1);
    leanh::lean_inc(v_snd_2597_);
    leanh::lean_dec(v___x_2596_);
    v___x_2598_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(v_snd_2597_, v_a_2588_);
    leanh::lean_dec(v_snd_2597_);
    v___x_2599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2599_, 0, v___x_2598_);
    return v___x_2599_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___boxed(
    mut v_ext_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(v_ext_2600_, v_a_2601_, v_a_2602_);
    leanh::lean_dec(v_a_2602_);
    leanh::lean_dec(v_a_2601_);
    leanh::lean_dec_ref(v_ext_2600_);
    return v_res_2604_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(
    mut v_cacheExt_2605_: *mut leanh::LeanObject,
    mut v_trivialType_2606_: *mut leanh::LeanObject,
    mut v_declName_2607_: *mut leanh::LeanObject,
    mut v_a_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_unused_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2611_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(v_cacheExt_2605_, v_declName_2607_, v_a_2609_);
                v_a_2612_ = leanh::lean_ctor_get(v___x_2611_, 0);
                v_isSharedCheck_2631_ = (!leanh::lean_is_exclusive(v___x_2611_)) as u8;
                if v_isSharedCheck_2631_ == 0 {
                    v___x_2614_ = v___x_2611_;
                    v_isShared_2615_ = v_isSharedCheck_2631_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2612_);
                    leanh::lean_dec(v___x_2611_);
                    v___x_2614_ = leanh::lean_box(0);
                    v_isShared_2615_ = v_isSharedCheck_2631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2612_) == 0 {
                    leanh::lean_del_object(v___x_2614_);
                    leanh::lean_inc(v_declName_2607_);
                    v___x_2616_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache(v_trivialType_2606_, v_declName_2607_, v_a_2608_, v_a_2609_);
                    if leanh::lean_obj_tag(v___x_2616_) == 0 {
                        v_a_2617_ = leanh::lean_ctor_get(v___x_2616_, 0);
                        leanh::lean_inc_n(v_a_2617_, 2);
                        leanh::lean_dec_ref_known(v___x_2616_, 1);
                        v___x_2618_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(v_cacheExt_2605_, v_declName_2607_, v_a_2617_, v_a_2609_);
                        v_isSharedCheck_2625_ =
                            (!leanh::lean_is_exclusive(v___x_2618_)) as u8;
                        if v_isSharedCheck_2625_ == 0 {
                            v_unused_2626_ = leanh::lean_ctor_get(v___x_2618_, 0);
                            leanh::lean_dec(v_unused_2626_);
                            v___x_2620_ = v___x_2618_;
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2618_);
                            v___x_2620_ = leanh::lean_box(0);
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_2607_);
                        leanh::lean_dec_ref(v_cacheExt_2605_);
                        return v___x_2616_;
                    }
                } else {
                    leanh::lean_dec(v_declName_2607_);
                    leanh::lean_dec_ref(v_trivialType_2606_);
                    leanh::lean_dec_ref(v_cacheExt_2605_);
                    v_val_2627_ = leanh::lean_ctor_get(v_a_2612_, 0);
                    leanh::lean_inc(v_val_2627_);
                    leanh::lean_dec_ref_known(v_a_2612_, 1);
                    if v_isShared_2615_ == 0 {
                        leanh::lean_ctor_set(v___x_2614_, 0, v_val_2627_);
                        v___x_2629_ = v___x_2614_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2630_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_val_2627_);
                        v___x_2629_ = v_reuseFailAlloc_2630_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2621_ == 0 {
                    leanh::lean_ctor_set(v___x_2620_, 0, v_a_2617_);
                    v___x_2623_ = v___x_2620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2617_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2623_;
            }
            4 => {
                return v___x_2629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f___boxed(
    mut v_cacheExt_2632_: *mut leanh::LeanObject,
    mut v_trivialType_2633_: *mut leanh::LeanObject,
    mut v_declName_2634_: *mut leanh::LeanObject,
    mut v_a_2635_: *mut leanh::LeanObject,
    mut v_a_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(
        v_cacheExt_2632_,
        v_trivialType_2633_,
        v_declName_2634_,
        v_a_2635_,
        v_a_2636_,
    );
    leanh::lean_dec(v_a_2636_);
    leanh::lean_dec_ref(v_a_2635_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0(
    mut v_ext_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(v_ext_2639_, v_a_2640_, v_a_2642_);
    return v___x_2644_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___boxed(
    mut v_ext_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
    mut v_a_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2650_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0(v_ext_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
    leanh::lean_dec(v_a_2648_);
    leanh::lean_dec_ref(v_a_2647_);
    leanh::lean_dec(v_a_2646_);
    leanh::lean_dec_ref(v_ext_2645_);
    return v_res_2650_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1(
    mut v_ext_2651_: *mut leanh::LeanObject,
    mut v_a_2652_: *mut leanh::LeanObject,
    mut v_b_2653_: *mut leanh::LeanObject,
    mut v_a_2654_: *mut leanh::LeanObject,
    mut v_a_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2657_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(v_ext_2651_, v_a_2652_, v_b_2653_, v_a_2655_);
    return v___x_2657_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___boxed(
    mut v_ext_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
    mut v_b_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1(v_ext_2658_, v_a_2659_, v_b_2660_, v_a_2661_, v_a_2662_);
    leanh::lean_dec(v_a_2662_);
    leanh::lean_dec_ref(v_a_2661_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0(
    mut v_00_u03b2_2665_: *mut leanh::LeanObject,
    mut v_x_2666_: *mut leanh::LeanObject,
    mut v_x_2667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(v_x_2666_, v_x_2667_);
    return v___x_2668_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2669_: *mut leanh::LeanObject,
    mut v_x_2670_: *mut leanh::LeanObject,
    mut v_x_2671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0(v_00_u03b2_2669_, v_x_2670_, v_x_2671_);
    leanh::lean_dec(v_x_2671_);
    leanh::lean_dec_ref(v_x_2670_);
    return v_res_2672_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2(
    mut v_00_u03b2_2673_: *mut leanh::LeanObject,
    mut v_x_2674_: *mut leanh::LeanObject,
    mut v_x_2675_: *mut leanh::LeanObject,
    mut v_x_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2___redArg(v_x_2674_, v_x_2675_, v_x_2676_);
    return v___x_2677_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2678_: *mut leanh::LeanObject,
    mut v_x_2679_: *mut leanh::LeanObject,
    mut v_x_2680_: usize,
    mut v_x_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(v_x_2679_, v_x_2680_, v_x_2681_);
    return v___x_2682_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2683_: *mut leanh::LeanObject,
    mut v_x_2684_: *mut leanh::LeanObject,
    mut v_x_2685_: *mut leanh::LeanObject,
    mut v_x_2686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1456__boxed_2687_: usize = 0;
    let mut v_res_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1456__boxed_2687_ = leanh::lean_unbox_usize(v_x_2685_);
    leanh::lean_dec(v_x_2685_);
    v_res_2688_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2683_, v_x_2684_, v_x_1456__boxed_2687_, v_x_2686_);
    leanh::lean_dec(v_x_2686_);
    leanh::lean_dec_ref(v_x_2684_);
    return v_res_2688_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2689_: *mut leanh::LeanObject,
    mut v_x_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: usize,
    mut v_x_2692_: usize,
    mut v_x_2693_: *mut leanh::LeanObject,
    mut v_x_2694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_x_2690_, v_x_2691_, v_x_2692_, v_x_2693_, v_x_2694_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_2696_: *mut leanh::LeanObject,
    mut v_x_2697_: *mut leanh::LeanObject,
    mut v_x_2698_: *mut leanh::LeanObject,
    mut v_x_2699_: *mut leanh::LeanObject,
    mut v_x_2700_: *mut leanh::LeanObject,
    mut v_x_2701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1467__boxed_2702_: usize = 0;
    let mut v_x_1468__boxed_2703_: usize = 0;
    let mut v_res_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1467__boxed_2702_ = leanh::lean_unbox_usize(v_x_2698_);
    leanh::lean_dec(v_x_2698_);
    v_x_1468__boxed_2703_ = leanh::lean_unbox_usize(v_x_2699_);
    leanh::lean_dec(v_x_2699_);
    v_res_2704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4(v_00_u03b2_2696_, v_x_2697_, v_x_1467__boxed_2702_, v_x_1468__boxed_2703_, v_x_2700_, v_x_2701_);
    return v_res_2704_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2705_: *mut leanh::LeanObject,
    mut v_keys_2706_: *mut leanh::LeanObject,
    mut v_vals_2707_: *mut leanh::LeanObject,
    mut v_heq_2708_: *mut leanh::LeanObject,
    mut v_i_2709_: *mut leanh::LeanObject,
    mut v_k_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2711_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2706_, v_vals_2707_, v_i_2709_, v_k_2710_);
    return v___x_2711_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2712_: *mut leanh::LeanObject,
    mut v_keys_2713_: *mut leanh::LeanObject,
    mut v_vals_2714_: *mut leanh::LeanObject,
    mut v_heq_2715_: *mut leanh::LeanObject,
    mut v_i_2716_: *mut leanh::LeanObject,
    mut v_k_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2712_, v_keys_2713_, v_vals_2714_, v_heq_2715_, v_i_2716_, v_k_2717_);
    leanh::lean_dec(v_k_2717_);
    leanh::lean_dec_ref(v_vals_2714_);
    leanh::lean_dec_ref(v_keys_2713_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2719_: *mut leanh::LeanObject,
    mut v_n_2720_: *mut leanh::LeanObject,
    mut v_k_2721_: *mut leanh::LeanObject,
    mut v_v_2722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6___redArg(v_n_2720_, v_k_2721_, v_v_2722_);
    return v___x_2723_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2724_: *mut leanh::LeanObject,
    mut v_depth_2725_: usize,
    mut v_keys_2726_: *mut leanh::LeanObject,
    mut v_vals_2727_: *mut leanh::LeanObject,
    mut v_heq_2728_: *mut leanh::LeanObject,
    mut v_i_2729_: *mut leanh::LeanObject,
    mut v_entries_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(v_depth_2725_, v_keys_2726_, v_vals_2727_, v_i_2729_, v_entries_2730_);
    return v___x_2731_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_2732_: *mut leanh::LeanObject,
    mut v_depth_2733_: *mut leanh::LeanObject,
    mut v_keys_2734_: *mut leanh::LeanObject,
    mut v_vals_2735_: *mut leanh::LeanObject,
    mut v_heq_2736_: *mut leanh::LeanObject,
    mut v_i_2737_: *mut leanh::LeanObject,
    mut v_entries_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2739_: usize = 0;
    let mut v_res_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2739_ = leanh::lean_unbox_usize(v_depth_2733_);
    leanh::lean_dec(v_depth_2733_);
    v_res_2740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_2732_, v_depth_boxed_2739_, v_keys_2734_, v_vals_2735_, v_heq_2736_, v_i_2737_, v_entries_2738_);
    leanh::lean_dec_ref(v_vals_2735_);
    leanh::lean_dec_ref(v_keys_2734_);
    return v_res_2740_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2741_: *mut leanh::LeanObject,
    mut v_x_2742_: *mut leanh::LeanObject,
    mut v_x_2743_: *mut leanh::LeanObject,
    mut v_x_2744_: *mut leanh::LeanObject,
    mut v_x_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2746_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2742_, v_x_2743_, v_x_2744_, v_x_2745_);
    return v___x_2746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Irrelevant(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Irrelevant(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Irrelevant(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
}