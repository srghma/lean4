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
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1: u64 = 0;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13_value: crate::leanh::LeanStringObject<82> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 114, 114, 101, 108, 101, 118, 97, 110, 116, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 103, 101, 116, 82, 101, 108, 101, 118, 97, 110, 116, 67, 116, 111, 114, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10_value:
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
    m_data: [110, 117, 109, 80, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__13_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__15_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instReprTrivialStructureInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0(
    mut v_k_1374_: *mut crate::leanh::LeanObject,
    mut v_b_1375_: *mut crate::leanh::LeanObject,
    mut v_c_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1380_);
    crate::leanh::lean_inc_ref(v___y_1379_);
    crate::leanh::lean_inc(v___y_1378_);
    crate::leanh::lean_inc_ref(v___y_1377_);
    v___x_1382_ = crate::leanh::lean_apply_7(
        v_k_1374_,
        v_b_1375_,
        v_c_1376_,
        v___y_1377_,
        v___y_1378_,
        v___y_1379_,
        v___y_1380_,
        crate::leanh::lean_box(0),
    );
    return v___x_1382_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0___boxed(
    mut v_k_1383_: *mut crate::leanh::LeanObject,
    mut v_b_1384_: *mut crate::leanh::LeanObject,
    mut v_c_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0(v_k_1383_, v_b_1384_, v_c_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
    crate::leanh::lean_dec(v___y_1389_);
    crate::leanh::lean_dec_ref(v___y_1388_);
    crate::leanh::lean_dec(v___y_1387_);
    crate::leanh::lean_dec_ref(v___y_1386_);
    return v_res_1391_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(
    mut v_type_1392_: *mut crate::leanh::LeanObject,
    mut v_k_1393_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1394_: u8,
    mut v_whnfType_1395_: u8,
    mut v___y_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1401_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1401_, 0, v_k_1393_);
                v___x_1402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1392_,
                    v___f_1401_,
                    v_cleanupAnnotations_1394_,
                    v_whnfType_1395_,
                    v___y_1396_,
                    v___y_1397_,
                    v___y_1398_,
                    v___y_1399_,
                );
                if crate::leanh::lean_obj_tag(v___x_1402_) == 0 {
                    v_a_1403_ = crate::leanh::lean_ctor_get(v___x_1402_, 0);
                    v_isSharedCheck_1410_ = (!crate::leanh::lean_is_exclusive(v___x_1402_)) as u8;
                    if v_isSharedCheck_1410_ == 0 {
                        v___x_1405_ = v___x_1402_;
                        v_isShared_1406_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1403_);
                        crate::leanh::lean_dec(v___x_1402_);
                        v___x_1405_ = crate::leanh::lean_box(0);
                        v_isShared_1406_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1411_ = crate::leanh::lean_ctor_get(v___x_1402_, 0);
                    v_isSharedCheck_1418_ = (!crate::leanh::lean_is_exclusive(v___x_1402_)) as u8;
                    if v_isSharedCheck_1418_ == 0 {
                        v___x_1413_ = v___x_1402_;
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1411_);
                        crate::leanh::lean_dec(v___x_1402_);
                        v___x_1413_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
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
                    v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
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
    mut v_type_1419_: *mut crate::leanh::LeanObject,
    mut v_k_1420_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1421_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1428_: u8 = 0;
    let mut v_whnfType_boxed_1429_: u8 = 0;
    let mut v_res_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1428_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1421_) as u8);
    v_whnfType_boxed_1429_ = (crate::leanh::lean_unbox(v_whnfType_1422_) as u8);
    v_res_1430_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(v_type_1419_, v_k_1420_, v_cleanupAnnotations_boxed_1428_, v_whnfType_boxed_1429_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
    crate::leanh::lean_dec(v___y_1426_);
    crate::leanh::lean_dec_ref(v___y_1425_);
    crate::leanh::lean_dec(v___y_1424_);
    crate::leanh::lean_dec_ref(v___y_1423_);
    return v_res_1430_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2(
    mut v_00_u03b1_1431_: *mut crate::leanh::LeanObject,
    mut v_type_1432_: *mut crate::leanh::LeanObject,
    mut v_k_1433_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1434_: u8,
    mut v_whnfType_1435_: u8,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(v_type_1432_, v_k_1433_, v_cleanupAnnotations_1434_, v_whnfType_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
    return v___x_1441_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___boxed(
    mut v_00_u03b1_1442_: *mut crate::leanh::LeanObject,
    mut v_type_1443_: *mut crate::leanh::LeanObject,
    mut v_k_1444_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1445_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1452_: u8 = 0;
    let mut v_whnfType_boxed_1453_: u8 = 0;
    let mut v_res_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1452_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1445_) as u8);
    v_whnfType_boxed_1453_ = (crate::leanh::lean_unbox(v_whnfType_1446_) as u8);
    v_res_1454_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2(v_00_u03b1_1442_, v_type_1443_, v_k_1444_, v_cleanupAnnotations_boxed_1452_, v_whnfType_boxed_1453_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    crate::leanh::lean_dec(v___y_1448_);
    crate::leanh::lean_dec_ref(v___y_1447_);
    return v_res_1454_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3(
    mut v_msg_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549__overap_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1460_ = l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___closed__0;
    v___x_2549__overap_1461_ = lean_panic_fn_borrowed(v___f_1460_, v_msg_1456_);
    crate::leanh::lean_inc(v___y_1458_);
    crate::leanh::lean_inc_ref(v___y_1457_);
    v___x_1462_ = crate::leanh::lean_apply_3(
        v___x_2549__overap_1461_,
        v___y_1457_,
        v___y_1458_,
        crate::leanh::lean_box(0),
    );
    return v___x_1462_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3___boxed(
    mut v_msg_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3(v_msg_1463_, v___y_1464_, v___y_1465_);
    crate::leanh::lean_dec(v___y_1465_);
    crate::leanh::lean_dec_ref(v___y_1464_);
    return v_res_1467_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(
    mut v_trivialType_1468_: *mut crate::leanh::LeanObject,
    mut v_a_1469_: *mut crate::leanh::LeanObject,
    mut v_b_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: u8 = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: u8 = 0;
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_a_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1476_ = crate::leanh::lean_ctor_get(v_a_1469_, 0);
                v_start_1477_ = crate::leanh::lean_ctor_get(v_a_1469_, 1);
                v_stop_1478_ = crate::leanh::lean_ctor_get(v_a_1469_, 2);
                v_isSharedCheck_1517_ = (!crate::leanh::lean_is_exclusive(v_a_1469_)) as u8;
                if v_isSharedCheck_1517_ == 0 {
                    v___x_1480_ = v_a_1469_;
                    v_isShared_1481_ = v_isSharedCheck_1517_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_1478_);
                    crate::leanh::lean_inc(v_start_1477_);
                    crate::leanh::lean_inc(v_array_1476_);
                    crate::leanh::lean_dec(v_a_1469_);
                    v___x_1480_ = crate::leanh::lean_box(0);
                    v_isShared_1481_ = v_isSharedCheck_1517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1482_ = lean_nat_dec_lt(v_start_1477_, v_stop_1478_);
                if v___x_1482_ == 0 {
                    crate::leanh::lean_del_object(v___x_1480_);
                    crate::leanh::lean_dec(v_stop_1478_);
                    crate::leanh::lean_dec(v_start_1477_);
                    crate::leanh::lean_dec_ref(v_array_1476_);
                    crate::leanh::lean_dec_ref(v_trivialType_1468_);
                    v___x_1483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1483_, 0, v_b_1470_);
                    return v___x_1483_;
                } else {
                    v___x_1484_ = lean_array_fget_borrowed(v_array_1476_, v_start_1477_);
                    crate::leanh::lean_inc(v___y_1474_);
                    crate::leanh::lean_inc_ref(v___y_1473_);
                    crate::leanh::lean_inc(v___y_1472_);
                    crate::leanh::lean_inc_ref(v___y_1471_);
                    crate::leanh::lean_inc(v___x_1484_);
                    v___x_1485_ = lean_infer_type(
                        v___x_1484_,
                        v___y_1471_,
                        v___y_1472_,
                        v___y_1473_,
                        v___y_1474_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1485_) == 0 {
                        v_a_1486_ = crate::leanh::lean_ctor_get(v___x_1485_, 0);
                        crate::leanh::lean_inc(v_a_1486_);
                        crate::leanh::lean_dec_ref_known(v___x_1485_, 1);
                        crate::leanh::lean_inc_ref(v_trivialType_1468_);
                        crate::leanh::lean_inc(v___y_1474_);
                        crate::leanh::lean_inc_ref(v___y_1473_);
                        crate::leanh::lean_inc(v___y_1472_);
                        crate::leanh::lean_inc_ref(v___y_1471_);
                        v___x_1487_ = crate::leanh::lean_apply_6(
                            v_trivialType_1468_,
                            v_a_1486_,
                            v___y_1471_,
                            v___y_1472_,
                            v___y_1473_,
                            v___y_1474_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_1487_) == 0 {
                            v_a_1488_ = crate::leanh::lean_ctor_get(v___x_1487_, 0);
                            crate::leanh::lean_inc(v_a_1488_);
                            crate::leanh::lean_dec_ref_known(v___x_1487_, 1);
                            v___x_1489_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1490_ = lean_nat_add(v_start_1477_, v___x_1489_);
                            crate::leanh::lean_dec(v_start_1477_);
                            if v_isShared_1481_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1480_, 1, v___x_1490_);
                                v___x_1492_ = v___x_1480_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1500_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1500_,
                                    0,
                                    v_array_1476_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1490_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1500_,
                                    2,
                                    v_stop_1478_,
                                );
                                v___x_1492_ = v_reuseFailAlloc_1500_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1480_);
                            crate::leanh::lean_dec(v_stop_1478_);
                            crate::leanh::lean_dec(v_start_1477_);
                            crate::leanh::lean_dec_ref(v_array_1476_);
                            crate::leanh::lean_dec_ref(v_b_1470_);
                            crate::leanh::lean_dec_ref(v_trivialType_1468_);
                            v_a_1501_ = crate::leanh::lean_ctor_get(v___x_1487_, 0);
                            v_isSharedCheck_1508_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1487_)) as u8;
                            if v_isSharedCheck_1508_ == 0 {
                                v___x_1503_ = v___x_1487_;
                                v_isShared_1504_ = v_isSharedCheck_1508_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1501_);
                                crate::leanh::lean_dec(v___x_1487_);
                                v___x_1503_ = crate::leanh::lean_box(0);
                                v_isShared_1504_ = v_isSharedCheck_1508_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1480_);
                        crate::leanh::lean_dec(v_stop_1478_);
                        crate::leanh::lean_dec(v_start_1477_);
                        crate::leanh::lean_dec_ref(v_array_1476_);
                        crate::leanh::lean_dec_ref(v_b_1470_);
                        crate::leanh::lean_dec_ref(v_trivialType_1468_);
                        v_a_1509_ = crate::leanh::lean_ctor_get(v___x_1485_, 0);
                        v_isSharedCheck_1516_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1485_)) as u8;
                        if v_isSharedCheck_1516_ == 0 {
                            v___x_1511_ = v___x_1485_;
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1509_);
                            crate::leanh::lean_dec(v___x_1485_);
                            v___x_1511_ = crate::leanh::lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1498_ = (crate::leanh::lean_unbox(v_a_1488_) as u8);
                crate::leanh::lean_dec(v_a_1488_);
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
                v___x_1495_ = crate::leanh::lean_box((v___y_1494_) as usize);
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
                    v_reuseFailAlloc_1507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
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
                    v_reuseFailAlloc_1515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
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
    mut v_trivialType_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v_b_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(v_trivialType_1518_, v_a_1519_, v_b_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    crate::leanh::lean_dec(v___y_1524_);
    crate::leanh::lean_dec_ref(v___y_1523_);
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    return v_res_1526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(
    mut v_trivialType_1529_: *mut crate::leanh::LeanObject,
    mut v_numParams_1530_: *mut crate::leanh::LeanObject,
    mut v_xs_1531_: *mut crate::leanh::LeanObject,
    mut v_x_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1538_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1539_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___closed__0;
                v___x_1545_ = lean_array_get_size(v_xs_1531_);
                v___x_1546_ = lean_nat_dec_le(v_numParams_1530_, v___x_1538_);
                if v___x_1546_ == 0 {
                    v_lower_1541_ = v_numParams_1530_;
                    v_upper_1542_ = v___x_1545_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_numParams_1530_);
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
    mut v_trivialType_1547_: *mut crate::leanh::LeanObject,
    mut v_numParams_1548_: *mut crate::leanh::LeanObject,
    mut v_xs_1549_: *mut crate::leanh::LeanObject,
    mut v_x_1550_: *mut crate::leanh::LeanObject,
    mut v___y_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1556_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(v_trivialType_1547_, v_numParams_1548_, v_xs_1549_, v_x_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
    crate::leanh::lean_dec(v___y_1554_);
    crate::leanh::lean_dec_ref(v___y_1553_);
    crate::leanh::lean_dec(v___y_1552_);
    crate::leanh::lean_dec_ref(v___y_1551_);
    crate::leanh::lean_dec_ref(v_x_1550_);
    return v_res_1556_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1557_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__0);
    v___x_1559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1);
    v___x_1561_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1562_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1562_, 0, v___x_1561_);
    crate::leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
    crate::leanh::lean_ctor_set(v___x_1562_, 2, v___x_1561_);
    crate::leanh::lean_ctor_set(v___x_1562_, 3, v___x_1561_);
    crate::leanh::lean_ctor_set(v___x_1562_, 4, v___x_1560_);
    crate::leanh::lean_ctor_set(v___x_1562_, 5, v___x_1560_);
    crate::leanh::lean_ctor_set(v___x_1562_, 6, v___x_1560_);
    crate::leanh::lean_ctor_set(v___x_1562_, 7, v___x_1560_);
    crate::leanh::lean_ctor_set(v___x_1562_, 8, v___x_1560_);
    crate::leanh::lean_ctor_set(v___x_1562_, 9, v___x_1560_);
    return v___x_1562_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
    v___x_1565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = 5usize;
    v___x_1567_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1568_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
    v___x_1570_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__3);
    v___x_1571_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1571_, 0, v___x_1570_);
    crate::leanh::lean_ctor_set(v___x_1571_, 1, v___x_1569_);
    crate::leanh::lean_ctor_set(v___x_1571_, 2, v___x_1567_);
    crate::leanh::lean_ctor_set(v___x_1571_, 3, v___x_1567_);
    crate::leanh::lean_ctor_set_usize(v___x_1571_, 4, v___x_1566_);
    return v___x_1571_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = crate::leanh::lean_box(1);
    v___x_1573_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4);
    v___x_1574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__1);
    v___x_1575_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
    crate::leanh::lean_ctor_set(v___x_1575_, 1, v___x_1573_);
    crate::leanh::lean_ctor_set(v___x_1575_, 2, v___x_1572_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10(
    mut v_msgData_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = lean_st_ref_get(v___y_1578_);
    v_env_1581_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
    crate::leanh::lean_inc_ref(v_env_1581_);
    crate::leanh::lean_dec(v___x_1580_);
    v_options_1582_ = crate::leanh::lean_ctor_get(v___y_1577_, 2);
    v___x_1583_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2);
    v___x_1584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5);
    crate::leanh::lean_inc_ref(v_options_1582_);
    v___x_1585_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1585_, 0, v_env_1581_);
    crate::leanh::lean_ctor_set(v___x_1585_, 1, v___x_1583_);
    crate::leanh::lean_ctor_set(v___x_1585_, 2, v___x_1584_);
    crate::leanh::lean_ctor_set(v___x_1585_, 3, v_options_1582_);
    v___x_1586_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1586_, 1, v_msgData_1576_);
    v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    return v___x_1587_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(
    mut v_msgData_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_1588_, v___y_1589_, v___y_1590_);
    crate::leanh::lean_dec(v___y_1590_);
    crate::leanh::lean_dec_ref(v___y_1589_);
    return v_res_1592_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(
    mut v_msg_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1597_ = crate::leanh::lean_ctor_get(v___y_1594_, 5);
                v___x_1598_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10(v_msg_1593_, v___y_1594_, v___y_1595_);
                v_a_1599_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                v_isSharedCheck_1607_ = (!crate::leanh::lean_is_exclusive(v___x_1598_)) as u8;
                if v_isSharedCheck_1607_ == 0 {
                    v___x_1601_ = v___x_1598_;
                    v_isShared_1602_ = v_isSharedCheck_1607_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1599_);
                    crate::leanh::lean_dec(v___x_1598_);
                    v___x_1601_ = crate::leanh::lean_box(0);
                    v_isShared_1602_ = v_isSharedCheck_1607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1597_);
                v___x_1603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1603_, 0, v_ref_1597_);
                crate::leanh::lean_ctor_set(v___x_1603_, 1, v_a_1599_);
                if v_isShared_1602_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1601_, 1);
                    crate::leanh::lean_ctor_set(v___x_1601_, 0, v___x_1603_);
                    v___x_1605_ = v___x_1601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
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
    mut v_msg_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1608_, v___y_1609_, v___y_1610_);
    crate::leanh::lean_dec(v___y_1610_);
    crate::leanh::lean_dec_ref(v___y_1609_);
    return v_res_1612_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(
    mut v_ref_1613_: *mut crate::leanh::LeanObject,
    mut v_msg_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1630_: u8 = 0;
    let mut v_cancelTk_x3f_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1632_: u8 = 0;
    let mut v_inheritedTraceOptions_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1618_ = crate::leanh::lean_ctor_get(v___y_1615_, 0);
    v_fileMap_1619_ = crate::leanh::lean_ctor_get(v___y_1615_, 1);
    v_options_1620_ = crate::leanh::lean_ctor_get(v___y_1615_, 2);
    v_currRecDepth_1621_ = crate::leanh::lean_ctor_get(v___y_1615_, 3);
    v_maxRecDepth_1622_ = crate::leanh::lean_ctor_get(v___y_1615_, 4);
    v_ref_1623_ = crate::leanh::lean_ctor_get(v___y_1615_, 5);
    v_currNamespace_1624_ = crate::leanh::lean_ctor_get(v___y_1615_, 6);
    v_openDecls_1625_ = crate::leanh::lean_ctor_get(v___y_1615_, 7);
    v_initHeartbeats_1626_ = crate::leanh::lean_ctor_get(v___y_1615_, 8);
    v_maxHeartbeats_1627_ = crate::leanh::lean_ctor_get(v___y_1615_, 9);
    v_quotContext_1628_ = crate::leanh::lean_ctor_get(v___y_1615_, 10);
    v_currMacroScope_1629_ = crate::leanh::lean_ctor_get(v___y_1615_, 11);
    v_diag_1630_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1615_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1631_ = crate::leanh::lean_ctor_get(v___y_1615_, 12);
    v_suppressElabErrors_1632_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1615_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1633_ = crate::leanh::lean_ctor_get(v___y_1615_, 13);
    v_ref_1634_ = l_Lean_replaceRef(v_ref_1613_, v_ref_1623_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1633_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1631_);
    crate::leanh::lean_inc(v_currMacroScope_1629_);
    crate::leanh::lean_inc(v_quotContext_1628_);
    crate::leanh::lean_inc(v_maxHeartbeats_1627_);
    crate::leanh::lean_inc(v_initHeartbeats_1626_);
    crate::leanh::lean_inc(v_openDecls_1625_);
    crate::leanh::lean_inc(v_currNamespace_1624_);
    crate::leanh::lean_inc(v_maxRecDepth_1622_);
    crate::leanh::lean_inc(v_currRecDepth_1621_);
    crate::leanh::lean_inc_ref(v_options_1620_);
    crate::leanh::lean_inc_ref(v_fileMap_1619_);
    crate::leanh::lean_inc_ref(v_fileName_1618_);
    v___x_1635_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1635_, 0, v_fileName_1618_);
    crate::leanh::lean_ctor_set(v___x_1635_, 1, v_fileMap_1619_);
    crate::leanh::lean_ctor_set(v___x_1635_, 2, v_options_1620_);
    crate::leanh::lean_ctor_set(v___x_1635_, 3, v_currRecDepth_1621_);
    crate::leanh::lean_ctor_set(v___x_1635_, 4, v_maxRecDepth_1622_);
    crate::leanh::lean_ctor_set(v___x_1635_, 5, v_ref_1634_);
    crate::leanh::lean_ctor_set(v___x_1635_, 6, v_currNamespace_1624_);
    crate::leanh::lean_ctor_set(v___x_1635_, 7, v_openDecls_1625_);
    crate::leanh::lean_ctor_set(v___x_1635_, 8, v_initHeartbeats_1626_);
    crate::leanh::lean_ctor_set(v___x_1635_, 9, v_maxHeartbeats_1627_);
    crate::leanh::lean_ctor_set(v___x_1635_, 10, v_quotContext_1628_);
    crate::leanh::lean_ctor_set(v___x_1635_, 11, v_currMacroScope_1629_);
    crate::leanh::lean_ctor_set(v___x_1635_, 12, v_cancelTk_x3f_1631_);
    crate::leanh::lean_ctor_set(v___x_1635_, 13, v_inheritedTraceOptions_1633_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1635_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1630_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1635_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1632_,
    );
    v___x_1636_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1614_, v___x_1635_, v___y_1616_);
    crate::leanh::lean_dec_ref_known(v___x_1635_, 14);
    return v___x_1636_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_ref_1637_: *mut crate::leanh::LeanObject,
    mut v_msg_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(v_ref_1637_, v_msg_1638_, v___y_1639_, v___y_1640_);
    crate::leanh::lean_dec(v___y_1640_);
    crate::leanh::lean_dec_ref(v___y_1639_);
    crate::leanh::lean_dec(v_ref_1637_);
    return v_res_1642_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__0;
    v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__2;
    v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__4;
    v___x_1651_ = l_Lean_stringToMessageData(v___x_1650_);
    return v___x_1651_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_1654_ = l_Lean_stringToMessageData(v___x_1653_);
    return v___x_1654_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
    return v___x_1657_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(
    mut v_msg_1664_: *mut crate::leanh::LeanObject,
    mut v_declHint_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u8 = 0;
    let mut v_isExporting_1671_: u8 = 0;
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = lean_st_ref_get(v___y_1666_);
                v_env_1669_ = crate::leanh::lean_ctor_get(v___x_1668_, 0);
                crate::leanh::lean_inc_ref(v_env_1669_);
                crate::leanh::lean_dec(v___x_1668_);
                v___x_1670_ = l_Lean_Name_isAnonymous(v_declHint_1665_);
                if v___x_1670_ == 0 {
                    v_isExporting_1671_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1669_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1671_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1669_);
                        crate::leanh::lean_dec(v_declHint_1665_);
                        v___x_1672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1672_, 0, v_msg_1664_);
                        return v___x_1672_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1669_);
                        v___x_1673_ = l_Lean_Environment_setExporting(v_env_1669_, v___x_1670_);
                        crate::leanh::lean_inc(v_declHint_1665_);
                        crate::leanh::lean_inc_ref(v___x_1673_);
                        v___x_1674_ = l_Lean_Environment_contains(
                            v___x_1673_,
                            v_declHint_1665_,
                            v_isExporting_1671_,
                        );
                        if v___x_1674_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1673_);
                            crate::leanh::lean_dec_ref(v_env_1669_);
                            crate::leanh::lean_dec(v_declHint_1665_);
                            v___x_1675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1675_, 0, v_msg_1664_);
                            return v___x_1675_;
                        } else {
                            v___x_1676_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__2);
                            v___x_1677_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__5);
                            v___x_1678_ = l_Lean_Options_empty;
                            v___x_1679_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1673_);
                            crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1676_);
                            crate::leanh::lean_ctor_set(v___x_1679_, 2, v___x_1677_);
                            crate::leanh::lean_ctor_set(v___x_1679_, 3, v___x_1678_);
                            crate::leanh::lean_inc(v_declHint_1665_);
                            v___x_1680_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1665_, v___x_1670_);
                            v_c_1681_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1681_, 0, v___x_1679_);
                            crate::leanh::lean_ctor_set(v_c_1681_, 1, v___x_1680_);
                            v___x_1682_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1669_,
                                v_declHint_1665_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1682_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1669_);
                                crate::leanh::lean_dec(v_declHint_1665_);
                                v___x_1683_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
                                v___x_1684_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1684_, 0, v___x_1683_);
                                crate::leanh::lean_ctor_set(v___x_1684_, 1, v_c_1681_);
                                v___x_1685_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
                                v___x_1686_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1686_, 0, v___x_1684_);
                                crate::leanh::lean_ctor_set(v___x_1686_, 1, v___x_1685_);
                                v___x_1687_ = l_Lean_MessageData_note(v___x_1686_);
                                v___x_1688_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1688_, 0, v_msg_1664_);
                                crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1687_);
                                v___x_1689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
                                return v___x_1689_;
                            } else {
                                v_val_1690_ = crate::leanh::lean_ctor_get(v___x_1682_, 0);
                                v_isSharedCheck_1725_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1682_)) as u8;
                                if v_isSharedCheck_1725_ == 0 {
                                    v___x_1692_ = v___x_1682_;
                                    v_isShared_1693_ = v_isSharedCheck_1725_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1690_);
                                    crate::leanh::lean_dec(v___x_1682_);
                                    v___x_1692_ = crate::leanh::lean_box(0);
                                    v_isShared_1693_ = v_isSharedCheck_1725_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1669_);
                    crate::leanh::lean_dec(v_declHint_1665_);
                    v___x_1726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1726_, 0, v_msg_1664_);
                    return v___x_1726_;
                }
            }
            1 => {
                v___x_1694_ = crate::leanh::lean_box(0);
                v___x_1695_ = l_Lean_Environment_header(v_env_1669_);
                crate::leanh::lean_dec_ref(v_env_1669_);
                v___x_1696_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1695_);
                v_mod_1697_ = lean_array_get(v___x_1694_, v___x_1696_, v_val_1690_);
                crate::leanh::lean_dec(v_val_1690_);
                crate::leanh::lean_dec_ref(v___x_1696_);
                v___x_1698_ = l_Lean_isPrivateName(v_declHint_1665_);
                crate::leanh::lean_dec(v_declHint_1665_);
                if v___x_1698_ == 0 {
                    v___x_1699_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
                    v___x_1700_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1700_, 0, v___x_1699_);
                    crate::leanh::lean_ctor_set(v___x_1700_, 1, v_c_1681_);
                    v___x_1701_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_1702_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1702_, 0, v___x_1700_);
                    crate::leanh::lean_ctor_set(v___x_1702_, 1, v___x_1701_);
                    v___x_1703_ = l_Lean_MessageData_ofName(v_mod_1697_);
                    v___x_1704_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1702_);
                    crate::leanh::lean_ctor_set(v___x_1704_, 1, v___x_1703_);
                    v___x_1705_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
                    v___x_1706_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1706_, 0, v___x_1704_);
                    crate::leanh::lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                    v___x_1707_ = l_Lean_MessageData_note(v___x_1706_);
                    v___x_1708_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1708_, 0, v_msg_1664_);
                    crate::leanh::lean_ctor_set(v___x_1708_, 1, v___x_1707_);
                    if v_isShared_1693_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1692_, 0);
                        crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1708_);
                        v___x_1710_ = v___x_1692_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1711_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1711_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
                    v___x_1713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1713_, 0, v___x_1712_);
                    crate::leanh::lean_ctor_set(v___x_1713_, 1, v_c_1681_);
                    v___x_1714_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_1715_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1715_, 0, v___x_1713_);
                    crate::leanh::lean_ctor_set(v___x_1715_, 1, v___x_1714_);
                    v___x_1716_ = l_Lean_MessageData_ofName(v_mod_1697_);
                    v___x_1717_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1715_);
                    crate::leanh::lean_ctor_set(v___x_1717_, 1, v___x_1716_);
                    v___x_1718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_1719_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1717_);
                    crate::leanh::lean_ctor_set(v___x_1719_, 1, v___x_1718_);
                    v___x_1720_ = l_Lean_MessageData_note(v___x_1719_);
                    v___x_1721_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1721_, 0, v_msg_1664_);
                    crate::leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                    if v_isShared_1693_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1692_, 0);
                        crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1721_);
                        v___x_1723_ = v___x_1692_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
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
    mut v_msg_1727_: *mut crate::leanh::LeanObject,
    mut v_declHint_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1727_, v_declHint_1728_, v___y_1729_);
    crate::leanh::lean_dec(v___y_1729_);
    return v_res_1731_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6(
    mut v_msg_1732_: *mut crate::leanh::LeanObject,
    mut v_declHint_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1732_, v_declHint_1733_, v___y_1735_);
                v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                if v_isSharedCheck_1747_ == 0 {
                    v___x_1740_ = v___x_1737_;
                    v_isShared_1741_ = v_isSharedCheck_1747_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1738_);
                    crate::leanh::lean_dec(v___x_1737_);
                    v___x_1740_ = crate::leanh::lean_box(0);
                    v_isShared_1741_ = v_isSharedCheck_1747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1742_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1743_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                crate::leanh::lean_ctor_set(v___x_1743_, 1, v_a_1738_);
                if v_isShared_1741_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1743_);
                    v___x_1745_ = v___x_1740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
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
    mut v_msg_1748_: *mut crate::leanh::LeanObject,
    mut v_declHint_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6(v_msg_1748_, v_declHint_1749_, v___y_1750_, v___y_1751_);
    crate::leanh::lean_dec(v___y_1751_);
    crate::leanh::lean_dec_ref(v___y_1750_);
    return v_res_1753_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(
    mut v_ref_1754_: *mut crate::leanh::LeanObject,
    mut v_msg_1755_: *mut crate::leanh::LeanObject,
    mut v_declHint_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6(v_msg_1755_, v_declHint_1756_, v___y_1757_, v___y_1758_);
    v_a_1761_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
    crate::leanh::lean_inc(v_a_1761_);
    crate::leanh::lean_dec_ref(v___x_1760_);
    v___x_1762_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(v_ref_1754_, v_a_1761_, v___y_1757_, v___y_1758_);
    return v___x_1762_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg___boxed(
    mut v_ref_1763_: *mut crate::leanh::LeanObject,
    mut v_msg_1764_: *mut crate::leanh::LeanObject,
    mut v_declHint_1765_: *mut crate::leanh::LeanObject,
    mut v___y_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(v_ref_1763_, v_msg_1764_, v_declHint_1765_, v___y_1766_, v___y_1767_);
    crate::leanh::lean_dec(v___y_1767_);
    crate::leanh::lean_dec_ref(v___y_1766_);
    crate::leanh::lean_dec(v_ref_1763_);
    return v_res_1769_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
    return v___x_1772_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(
    mut v_ref_1776_: *mut crate::leanh::LeanObject,
    mut v_constName_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_1782_ = 0;
    crate::leanh::lean_inc(v_constName_1777_);
    v___x_1783_ = l_Lean_MessageData_ofConstName(v_constName_1777_, v___x_1782_);
    v___x_1784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1781_);
    crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
    v___x_1785_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_1786_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1786_, 0, v___x_1784_);
    crate::leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
    v___x_1787_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(v_ref_1776_, v___x_1786_, v_constName_1777_, v___y_1778_, v___y_1779_);
    return v___x_1787_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_1788_: *mut crate::leanh::LeanObject,
    mut v_constName_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1793_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(v_ref_1788_, v_constName_1789_, v___y_1790_, v___y_1791_);
    crate::leanh::lean_dec(v___y_1791_);
    crate::leanh::lean_dec_ref(v___y_1790_);
    crate::leanh::lean_dec(v_ref_1788_);
    return v_res_1793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(
    mut v_constName_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1798_ = crate::leanh::lean_ctor_get(v___y_1795_, 5);
    v___x_1799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(v_ref_1798_, v_constName_1794_, v___y_1795_, v___y_1796_);
    return v___x_1799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg___boxed(
    mut v_constName_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(v_constName_1800_, v___y_1801_, v___y_1802_);
    crate::leanh::lean_dec(v___y_1802_);
    crate::leanh::lean_dec_ref(v___y_1801_);
    return v_res_1804_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(
    mut v_constName_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1809_ = lean_st_ref_get(v___y_1807_);
                v_env_1810_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                crate::leanh::lean_inc_ref(v_env_1810_);
                crate::leanh::lean_dec(v___x_1809_);
                v___x_1811_ = 0;
                crate::leanh::lean_inc(v_constName_1805_);
                v___x_1812_ =
                    l_Lean_Environment_find_x3f(v_env_1810_, v_constName_1805_, v___x_1811_);
                if crate::leanh::lean_obj_tag(v___x_1812_) == 0 {
                    v___x_1813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(v_constName_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1813_;
                } else {
                    crate::leanh::lean_dec(v_constName_1805_);
                    v_val_1814_ = crate::leanh::lean_ctor_get(v___x_1812_, 0);
                    v_isSharedCheck_1821_ = (!crate::leanh::lean_is_exclusive(v___x_1812_)) as u8;
                    if v_isSharedCheck_1821_ == 0 {
                        v___x_1816_ = v___x_1812_;
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1814_);
                        crate::leanh::lean_dec(v___x_1812_);
                        v___x_1816_ = crate::leanh::lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1817_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1816_, 0);
                    v___x_1819_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_val_1814_);
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
    mut v_constName_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(v_constName_1822_, v___y_1823_, v___y_1824_);
    crate::leanh::lean_dec(v___y_1824_);
    crate::leanh::lean_dec_ref(v___y_1823_);
    return v_res_1826_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1()
-> u64 {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u64 = 0;
    v___x_1833_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
    v___x_1834_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: u64 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__1);
    v___x_1836_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
    v___x_1837_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1836_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_1837_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1835_,
    );
    return v___x_1837_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1838_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__3);
    v___x_1840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1840_, 0, v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = crate::leanh::lean_box(1);
    v___x_1842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4);
    v___x_1843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1844_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1844_, 0, v___x_1843_);
    crate::leanh::lean_ctor_set(v___x_1844_, 1, v___x_1842_);
    crate::leanh::lean_ctor_set(v___x_1844_, 2, v___x_1841_);
    return v___x_1844_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = 1;
    v___x_1848_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1849_ = crate::leanh::lean_box(0);
    v___x_1850_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
    v___x_1851_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__5);
    v___x_1852_ = crate::leanh::lean_box(1);
    v___x_1853_ = 0;
    v___x_1854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__2);
    v___x_1855_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
    crate::leanh::lean_ctor_set(v___x_1855_, 1, v___x_1852_);
    crate::leanh::lean_ctor_set(v___x_1855_, 2, v___x_1851_);
    crate::leanh::lean_ctor_set(v___x_1855_, 3, v___x_1850_);
    crate::leanh::lean_ctor_set(v___x_1855_, 4, v___x_1849_);
    crate::leanh::lean_ctor_set(v___x_1855_, 5, v___x_1848_);
    crate::leanh::lean_ctor_set(v___x_1855_, 6, v___x_1849_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_1853_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v___x_1853_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v___x_1853_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_1847_,
    );
    return v___x_1855_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1857_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1858_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1858_, 0, v___x_1857_);
    crate::leanh::lean_ctor_set(v___x_1858_, 1, v___x_1857_);
    crate::leanh::lean_ctor_set(v___x_1858_, 2, v___x_1857_);
    crate::leanh::lean_ctor_set(v___x_1858_, 3, v___x_1857_);
    crate::leanh::lean_ctor_set(v___x_1858_, 4, v___x_1856_);
    crate::leanh::lean_ctor_set(v___x_1858_, 5, v___x_1856_);
    crate::leanh::lean_ctor_set(v___x_1858_, 6, v___x_1856_);
    crate::leanh::lean_ctor_set(v___x_1858_, 7, v___x_1856_);
    crate::leanh::lean_ctor_set(v___x_1858_, 8, v___x_1856_);
    crate::leanh::lean_ctor_set(v___x_1858_, 9, v___x_1856_);
    return v___x_1858_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 1, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 2, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 3, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 4, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 5, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
    v___x_1862_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    crate::leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
    crate::leanh::lean_ctor_set(v___x_1862_, 2, v___x_1861_);
    crate::leanh::lean_ctor_set(v___x_1862_, 3, v___x_1861_);
    crate::leanh::lean_ctor_set(v___x_1862_, 4, v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__10);
    v___x_1864_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9_spec__10___closed__4);
    v___x_1865_ = crate::leanh::lean_box(1);
    v___x_1866_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__9);
    v___x_1867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__8);
    v___x_1868_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    crate::leanh::lean_ctor_set(v___x_1868_, 1, v___x_1866_);
    crate::leanh::lean_ctor_set(v___x_1868_, 2, v___x_1865_);
    crate::leanh::lean_ctor_set(v___x_1868_, 3, v___x_1864_);
    crate::leanh::lean_ctor_set(v___x_1868_, 4, v___x_1863_);
    return v___x_1868_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
    v___x_1873_ = crate::leanh::lean_unsigned_to_nat(47);
    v___x_1874_ = crate::leanh::lean_unsigned_to_nat(21);
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
    mut v_ctorName_1878_: *mut crate::leanh::LeanObject,
    mut v_trivialType_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(v_ctorName_1878_, v_a_1880_, v_a_1881_);
                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    crate::leanh::lean_inc(v_a_1884_);
                    crate::leanh::lean_dec_ref_known(v___x_1883_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1884_) == 6 {
                        v_val_1885_ = crate::leanh::lean_ctor_get(v_a_1884_, 0);
                        crate::leanh::lean_inc_ref(v_val_1885_);
                        crate::leanh::lean_dec_ref_known(v_a_1884_, 1);
                        v___x_1886_ = 0;
                        v___x_1887_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__7);
                        v___x_1888_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__11);
                        v___x_1889_ = lean_st_mk_ref(v___x_1888_);
                        v_toConstantVal_1890_ = crate::leanh::lean_ctor_get(v_val_1885_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_1890_);
                        v_numParams_1891_ = crate::leanh::lean_ctor_get(v_val_1885_, 3);
                        crate::leanh::lean_inc(v_numParams_1891_);
                        crate::leanh::lean_dec_ref(v_val_1885_);
                        v_type_1892_ = crate::leanh::lean_ctor_get(v_toConstantVal_1890_, 2);
                        crate::leanh::lean_inc_ref(v_type_1892_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_1890_);
                        v___f_1893_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                        crate::leanh::lean_closure_set(v___f_1893_, 0, v_trivialType_1879_);
                        crate::leanh::lean_closure_set(v___f_1893_, 1, v_numParams_1891_);
                        v___x_1894_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__2___redArg(v_type_1892_, v___f_1893_, v___x_1886_, v___x_1886_, v___x_1887_, v___x_1889_, v_a_1880_, v_a_1881_);
                        if crate::leanh::lean_obj_tag(v___x_1894_) == 0 {
                            v_a_1895_ = crate::leanh::lean_ctor_get(v___x_1894_, 0);
                            v_isSharedCheck_1903_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1894_)) as u8;
                            if v_isSharedCheck_1903_ == 0 {
                                v___x_1897_ = v___x_1894_;
                                v_isShared_1898_ = v_isSharedCheck_1903_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1895_);
                                crate::leanh::lean_dec(v___x_1894_);
                                v___x_1897_ = crate::leanh::lean_box(0);
                                v_isShared_1898_ = v_isSharedCheck_1903_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1889_);
                            return v___x_1894_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1884_);
                        crate::leanh::lean_dec_ref(v_trivialType_1879_);
                        v___x_1904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15_once), _init_l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields___closed__15);
                        v___x_1905_ = l_panic___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__3(v___x_1904_, v_a_1880_, v_a_1881_);
                        return v___x_1905_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_trivialType_1879_);
                    v_a_1906_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1913_ = (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1908_ = v___x_1883_;
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1906_);
                        crate::leanh::lean_dec(v___x_1883_);
                        v___x_1908_ = crate::leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1899_ = lean_st_ref_get(v___x_1889_);
                crate::leanh::lean_dec(v___x_1889_);
                crate::leanh::lean_dec(v___x_1899_);
                if v_isShared_1898_ == 0 {
                    v___x_1901_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1895_);
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
                    v_reuseFailAlloc_1912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
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
    mut v_ctorName_1914_: *mut crate::leanh::LeanObject,
    mut v_trivialType_1915_: *mut crate::leanh::LeanObject,
    mut v_a_1916_: *mut crate::leanh::LeanObject,
    mut v_a_1917_: *mut crate::leanh::LeanObject,
    mut v_a_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ =
        l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields(
            v_ctorName_1914_,
            v_trivialType_1915_,
            v_a_1916_,
            v_a_1917_,
        );
    crate::leanh::lean_dec(v_a_1917_);
    crate::leanh::lean_dec_ref(v_a_1916_);
    return v_res_1919_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(
    mut v_trivialType_1920_: *mut crate::leanh::LeanObject,
    mut v_inst_1921_: *mut crate::leanh::LeanObject,
    mut v_R_1922_: *mut crate::leanh::LeanObject,
    mut v_a_1923_: *mut crate::leanh::LeanObject,
    mut v_b_1924_: *mut crate::leanh::LeanObject,
    mut v_c_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___redArg(v_trivialType_1920_, v_a_1923_, v_b_1924_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
    return v___x_1931_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___boxed(
    mut v_trivialType_1932_: *mut crate::leanh::LeanObject,
    mut v_inst_1933_: *mut crate::leanh::LeanObject,
    mut v_R_1934_: *mut crate::leanh::LeanObject,
    mut v_a_1935_: *mut crate::leanh::LeanObject,
    mut v_b_1936_: *mut crate::leanh::LeanObject,
    mut v_c_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(v_trivialType_1932_, v_inst_1933_, v_R_1934_, v_a_1935_, v_b_1936_, v_c_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
    crate::leanh::lean_dec(v___y_1941_);
    crate::leanh::lean_dec_ref(v___y_1940_);
    crate::leanh::lean_dec(v___y_1939_);
    crate::leanh::lean_dec_ref(v___y_1938_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0(
    mut v_00_u03b1_1944_: *mut crate::leanh::LeanObject,
    mut v_constName_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___redArg(v_constName_1945_, v___y_1946_, v___y_1947_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0___boxed(
    mut v_00_u03b1_1950_: *mut crate::leanh::LeanObject,
    mut v_constName_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0(v_00_u03b1_1950_, v_constName_1951_, v___y_1952_, v___y_1953_);
    crate::leanh::lean_dec(v___y_1953_);
    crate::leanh::lean_dec_ref(v___y_1952_);
    return v_res_1955_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3(
    mut v_00_u03b1_1956_: *mut crate::leanh::LeanObject,
    mut v_ref_1957_: *mut crate::leanh::LeanObject,
    mut v_constName_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___redArg(v_ref_1957_, v_constName_1958_, v___y_1959_, v___y_1960_);
    return v___x_1962_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_1963_: *mut crate::leanh::LeanObject,
    mut v_ref_1964_: *mut crate::leanh::LeanObject,
    mut v_constName_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3(v_00_u03b1_1963_, v_ref_1964_, v_constName_1965_, v___y_1966_, v___y_1967_);
    crate::leanh::lean_dec(v___y_1967_);
    crate::leanh::lean_dec_ref(v___y_1966_);
    crate::leanh::lean_dec(v_ref_1964_);
    return v_res_1969_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5(
    mut v_00_u03b1_1970_: *mut crate::leanh::LeanObject,
    mut v_ref_1971_: *mut crate::leanh::LeanObject,
    mut v_msg_1972_: *mut crate::leanh::LeanObject,
    mut v_declHint_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___redArg(v_ref_1971_, v_msg_1972_, v_declHint_1973_, v___y_1974_, v___y_1975_);
    return v___x_1977_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5___boxed(
    mut v_00_u03b1_1978_: *mut crate::leanh::LeanObject,
    mut v_ref_1979_: *mut crate::leanh::LeanObject,
    mut v_msg_1980_: *mut crate::leanh::LeanObject,
    mut v_declHint_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1985_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5(v_00_u03b1_1978_, v_ref_1979_, v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_);
    crate::leanh::lean_dec(v___y_1983_);
    crate::leanh::lean_dec_ref(v___y_1982_);
    crate::leanh::lean_dec(v_ref_1979_);
    return v_res_1985_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7(
    mut v_msg_1986_: *mut crate::leanh::LeanObject,
    mut v_declHint_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1986_, v_declHint_1987_, v___y_1989_);
    return v___x_1991_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7___boxed(
    mut v_msg_1992_: *mut crate::leanh::LeanObject,
    mut v_declHint_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__6_spec__7(v_msg_1992_, v_declHint_1993_, v___y_1994_, v___y_1995_);
    crate::leanh::lean_dec(v___y_1995_);
    crate::leanh::lean_dec_ref(v___y_1994_);
    return v_res_1997_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7(
    mut v_00_u03b1_1998_: *mut crate::leanh::LeanObject,
    mut v_ref_1999_: *mut crate::leanh::LeanObject,
    mut v_msg_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___redArg(v_ref_1999_, v_msg_2000_, v___y_2001_, v___y_2002_);
    return v___x_2004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_2005_: *mut crate::leanh::LeanObject,
    mut v_ref_2006_: *mut crate::leanh::LeanObject,
    mut v_msg_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
    mut v___y_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7(v_00_u03b1_2005_, v_ref_2006_, v_msg_2007_, v___y_2008_, v___y_2009_);
    crate::leanh::lean_dec(v___y_2009_);
    crate::leanh::lean_dec_ref(v___y_2008_);
    crate::leanh::lean_dec(v_ref_2006_);
    return v_res_2011_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(
    mut v_00_u03b1_2012_: *mut crate::leanh::LeanObject,
    mut v_msg_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_2013_, v___y_2014_, v___y_2015_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_2018_: *mut crate::leanh::LeanObject,
    mut v_msg_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2023_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_2018_, v_msg_2019_, v___y_2020_, v___y_2021_);
    crate::leanh::lean_dec(v___y_2021_);
    crate::leanh::lean_dec_ref(v___y_2020_);
    return v_res_2023_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr_spec__0(
    mut v_a_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = lean_nat_to_int(v_a_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2045_ = lean_nat_to_int(v___x_2044_);
    return v___x_2045_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_2053_ = lean_nat_to_int(v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__0;
    v___x_2059_ = lean_string_length(v___x_2058_);
    return v___x_2059_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ = crate::leanh::lean_obj_once(
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
    mut v_x_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctorName_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldIdx_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctorName_2067_ = crate::leanh::lean_ctor_get(v_x_2066_, 0);
    crate::leanh::lean_inc(v_ctorName_2067_);
    v_numParams_2068_ = crate::leanh::lean_ctor_get(v_x_2066_, 1);
    crate::leanh::lean_inc(v_numParams_2068_);
    v_fieldIdx_2069_ = crate::leanh::lean_ctor_get(v_x_2066_, 2);
    crate::leanh::lean_inc(v_fieldIdx_2069_);
    crate::leanh::lean_dec_ref(v_x_2066_);
    v___x_2070_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__5;
    v___x_2071_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__6;
    v___x_2072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__7,
    );
    v___x_2073_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2074_ = l_Lean_Name_reprPrec(v_ctorName_2067_, v___x_2073_);
    v___x_2075_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2075_, 0, v___x_2072_);
    crate::leanh::lean_ctor_set(v___x_2075_, 1, v___x_2074_);
    v___x_2076_ = 0;
    v___x_2077_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2075_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2077_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    v___x_2078_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2078_, 0, v___x_2071_);
    crate::leanh::lean_ctor_set(v___x_2078_, 1, v___x_2077_);
    v___x_2079_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__9;
    v___x_2080_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2080_, 0, v___x_2078_);
    crate::leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
    v___x_2081_ = crate::leanh::lean_box(1);
    v___x_2082_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2082_, 0, v___x_2080_);
    crate::leanh::lean_ctor_set(v___x_2082_, 1, v___x_2081_);
    v___x_2083_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__11;
    v___x_2084_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2082_);
    crate::leanh::lean_ctor_set(v___x_2084_, 1, v___x_2083_);
    v___x_2085_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2084_);
    crate::leanh::lean_ctor_set(v___x_2085_, 1, v___x_2070_);
    v___x_2086_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__12,
    );
    v___x_2087_ = l_Nat_reprFast(v_numParams_2068_);
    v___x_2088_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
    v___x_2089_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2086_);
    crate::leanh::lean_ctor_set(v___x_2089_, 1, v___x_2088_);
    v___x_2090_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2090_, 0, v___x_2089_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2090_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    v___x_2091_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2091_, 0, v___x_2085_);
    crate::leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
    v___x_2092_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2092_, 0, v___x_2091_);
    crate::leanh::lean_ctor_set(v___x_2092_, 1, v___x_2079_);
    v___x_2093_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2093_, 0, v___x_2092_);
    crate::leanh::lean_ctor_set(v___x_2093_, 1, v___x_2081_);
    v___x_2094_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__14;
    v___x_2095_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2095_, 0, v___x_2093_);
    crate::leanh::lean_ctor_set(v___x_2095_, 1, v___x_2094_);
    v___x_2096_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2096_, 0, v___x_2095_);
    crate::leanh::lean_ctor_set(v___x_2096_, 1, v___x_2070_);
    v___x_2097_ = l_Nat_reprFast(v_fieldIdx_2069_);
    v___x_2098_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2098_, 0, v___x_2097_);
    v___x_2099_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2099_, 0, v___x_2072_);
    crate::leanh::lean_ctor_set(v___x_2099_, 1, v___x_2098_);
    v___x_2100_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2100_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    v___x_2101_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2096_);
    crate::leanh::lean_ctor_set(v___x_2101_, 1, v___x_2100_);
    v___x_2102_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17_once
        ),
        _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__17,
    );
    v___x_2103_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__18;
    v___x_2104_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2103_);
    crate::leanh::lean_ctor_set(v___x_2104_, 1, v___x_2101_);
    v___x_2105_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg___closed__19;
    v___x_2106_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2104_);
    crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2105_);
    v___x_2107_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2102_);
    crate::leanh::lean_ctor_set(v___x_2107_, 1, v___x_2106_);
    v___x_2108_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2107_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2108_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2076_,
    );
    return v___x_2108_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr(
    mut v_x_2109_: *mut crate::leanh::LeanObject,
    mut v_prec_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2111_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___redArg(v_x_2109_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr___boxed(
    mut v_x_2112_: *mut crate::leanh::LeanObject,
    mut v_prec_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo_repr(v_x_2112_, v_prec_2113_);
    crate::leanh::lean_dec(v_prec_2113_);
    return v_res_2114_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(
    mut v_upperBound_2119_: *mut crate::leanh::LeanObject,
    mut v_val_2120_: *mut crate::leanh::LeanObject,
    mut v_head_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v___x_2123_: u8,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
    mut v_b_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: u8 = 0;
    let mut v_numParams_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_unused_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2132_ = lean_nat_dec_lt(v_a_2124_, v_upperBound_2119_);
                if v___x_2132_ == 0 {
                    crate::leanh::lean_dec(v_a_2124_);
                    crate::leanh::lean_dec(v_head_2121_);
                    v___x_2133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2133_, 0, v_b_2125_);
                    return v___x_2133_;
                } else {
                    v_snd_2134_ = crate::leanh::lean_ctor_get(v_b_2125_, 1);
                    v_isSharedCheck_2158_ = (!crate::leanh::lean_is_exclusive(v_b_2125_)) as u8;
                    if v_isSharedCheck_2158_ == 0 {
                        v_unused_2159_ = crate::leanh::lean_ctor_get(v_b_2125_, 0);
                        crate::leanh::lean_dec(v_unused_2159_);
                        v___x_2136_ = v_b_2125_;
                        v_isShared_2137_ = v_isSharedCheck_2158_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2134_);
                        crate::leanh::lean_dec(v_b_2125_);
                        v___x_2136_ = crate::leanh::lean_box(0);
                        v_isShared_2137_ = v_isSharedCheck_2158_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2129_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2130_ = lean_nat_add(v_a_2124_, v___x_2129_);
                crate::leanh::lean_dec(v_a_2124_);
                v_a_2124_ = v___x_2130_;
                v_b_2125_ = v_a_2128_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2138_ = crate::leanh::lean_box(0);
                v___x_2139_ = lean_array_fget_borrowed(v_a_2122_, v_a_2124_);
                v___x_2140_ = (crate::leanh::lean_unbox(v___x_2139_) as u8);
                if v___x_2140_ == 0 {
                    if v_isShared_2137_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2138_);
                        v___x_2142_ = v___x_2136_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2138_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_snd_2134_);
                        v___x_2142_ = v_reuseFailAlloc_2143_;
                        state = 3;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_snd_2134_) == 0 {
                        v___y_2145_ = v___x_2123_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2157_ = (crate::leanh::lean_unbox(v___x_2139_) as u8);
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
                    crate::leanh::lean_dec(v_snd_2134_);
                    v_numParams_2146_ = crate::leanh::lean_ctor_get(v_val_2120_, 1);
                    crate::leanh::lean_inc(v_a_2124_);
                    crate::leanh::lean_inc(v_numParams_2146_);
                    crate::leanh::lean_inc(v_head_2121_);
                    v___x_2147_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2147_, 0, v_head_2121_);
                    crate::leanh::lean_ctor_set(v___x_2147_, 1, v_numParams_2146_);
                    crate::leanh::lean_ctor_set(v___x_2147_, 2, v_a_2124_);
                    v___x_2148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2148_, 0, v___x_2147_);
                    if v_isShared_2137_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2136_, 1, v___x_2148_);
                        crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2138_);
                        v___x_2150_ = v___x_2136_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2151_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2138_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2148_);
                        v___x_2150_ = v_reuseFailAlloc_2151_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2124_);
                    crate::leanh::lean_dec(v_head_2121_);
                    v___x_2152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___closed__0;
                    if v_isShared_2137_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2152_);
                        v___x_2154_ = v___x_2136_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2152_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_snd_2134_);
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
                v___x_2155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                return v___x_2155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg___boxed(
    mut v_upperBound_2160_: *mut crate::leanh::LeanObject,
    mut v_val_2161_: *mut crate::leanh::LeanObject,
    mut v_head_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v___x_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_b_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4263__boxed_2168_: u8 = 0;
    let mut v_res_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4263__boxed_2168_ = (crate::leanh::lean_unbox(v___x_2164_) as u8);
    v_res_2169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(v_upperBound_2160_, v_val_2161_, v_head_2162_, v_a_2163_, v___x_4263__boxed_2168_, v_a_2165_, v_b_2166_);
    crate::leanh::lean_dec_ref(v_a_2163_);
    crate::leanh::lean_dec_ref(v_val_2161_);
    crate::leanh::lean_dec(v_upperBound_2160_);
    return v_res_2169_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache(
    mut v_trivialType_2172_: *mut crate::leanh::LeanObject,
    mut v_declName_2173_: *mut crate::leanh::LeanObject,
    mut v_a_2174_: *mut crate::leanh::LeanObject,
    mut v_a_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_2192_: u8 = 0;
    let mut v_isRec_2193_: u8 = 0;
    let mut v_ctors_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v_fst_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut v_a_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2231_: u8 = 0;
    let mut v_a_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_a_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut v_a_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2259_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2180_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_declName_2173_);
                if v___x_2180_ == 0 {
                    v___x_2181_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(v_declName_2173_, v_a_2174_, v_a_2175_);
                    if crate::leanh::lean_obj_tag(v___x_2181_) == 0 {
                        v_a_2182_ = crate::leanh::lean_ctor_get(v___x_2181_, 0);
                        v_isSharedCheck_2255_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2181_)) as u8;
                        if v_isSharedCheck_2255_ == 0 {
                            v___x_2184_ = v___x_2181_;
                            v_isShared_2185_ = v_isSharedCheck_2255_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2182_);
                            crate::leanh::lean_dec(v___x_2181_);
                            v___x_2184_ = crate::leanh::lean_box(0);
                            v_isShared_2185_ = v_isSharedCheck_2255_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_trivialType_2172_);
                        v_a_2256_ = crate::leanh::lean_ctor_get(v___x_2181_, 0);
                        v_isSharedCheck_2263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2181_)) as u8;
                        if v_isSharedCheck_2263_ == 0 {
                            v___x_2258_ = v___x_2181_;
                            v_isShared_2259_ = v_isSharedCheck_2263_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2256_);
                            crate::leanh::lean_dec(v___x_2181_);
                            v___x_2258_ = crate::leanh::lean_box(0);
                            v_isShared_2259_ = v_isSharedCheck_2263_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2173_);
                    crate::leanh::lean_dec_ref(v_trivialType_2172_);
                    v___x_2264_ = crate::leanh::lean_box(0);
                    v___x_2265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2265_, 0, v___x_2264_);
                    return v___x_2265_;
                }
            }
            1 => {
                v___x_2178_ = crate::leanh::lean_box(0);
                v___x_2179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2179_, 0, v___x_2178_);
                return v___x_2179_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2182_) == 5 {
                    v_val_2191_ = crate::leanh::lean_ctor_get(v_a_2182_, 0);
                    crate::leanh::lean_inc_ref(v_val_2191_);
                    crate::leanh::lean_dec_ref_known(v_a_2182_, 1);
                    v_isUnsafe_2192_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2191_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
                    );
                    if v_isUnsafe_2192_ == 0 {
                        v_isRec_2193_ = crate::leanh::lean_ctor_get_uint8(
                            v_val_2191_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        );
                        if v_isRec_2193_ == 0 {
                            crate::leanh::lean_del_object(v___x_2184_);
                            v_ctors_2194_ = crate::leanh::lean_ctor_get(v_val_2191_, 4);
                            if crate::leanh::lean_obj_tag(v_ctors_2194_) == 1 {
                                v_tail_2195_ = crate::leanh::lean_ctor_get(v_ctors_2194_, 1);
                                if crate::leanh::lean_obj_tag(v_tail_2195_) == 0 {
                                    v_head_2196_ = crate::leanh::lean_ctor_get(v_ctors_2194_, 0);
                                    crate::leanh::lean_inc_n(v_head_2196_, 2);
                                    v___x_2197_ = crate::leanh::lean_box(0);
                                    v___x_2198_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                                        v_head_2196_,
                                        v___x_2197_,
                                        v_a_2174_,
                                        v_a_2175_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2198_) == 0 {
                                        v_a_2199_ = crate::leanh::lean_ctor_get(v___x_2198_, 0);
                                        v_isSharedCheck_2244_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2198_)) as u8;
                                        if v_isSharedCheck_2244_ == 0 {
                                            v___x_2201_ = v___x_2198_;
                                            v_isShared_2202_ = v_isSharedCheck_2244_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2199_);
                                            crate::leanh::lean_dec(v___x_2198_);
                                            v___x_2201_ = crate::leanh::lean_box(0);
                                            v_isShared_2202_ = v_isSharedCheck_2244_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_head_2196_);
                                        crate::leanh::lean_dec_ref(v_val_2191_);
                                        crate::leanh::lean_dec_ref(v_trivialType_2172_);
                                        v_a_2245_ = crate::leanh::lean_ctor_get(v___x_2198_, 0);
                                        v_isSharedCheck_2252_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2198_)) as u8;
                                        if v_isSharedCheck_2252_ == 0 {
                                            v___x_2247_ = v___x_2198_;
                                            v_isShared_2248_ = v_isSharedCheck_2252_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2245_);
                                            crate::leanh::lean_dec(v___x_2198_);
                                            v___x_2247_ = crate::leanh::lean_box(0);
                                            v_isShared_2248_ = v_isSharedCheck_2252_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_val_2191_);
                                    crate::leanh::lean_dec_ref(v_trivialType_2172_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_val_2191_);
                                crate::leanh::lean_dec_ref(v_trivialType_2172_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_val_2191_);
                            crate::leanh::lean_dec_ref(v_trivialType_2172_);
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_val_2191_);
                        crate::leanh::lean_dec_ref(v_trivialType_2172_);
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2184_);
                    crate::leanh::lean_dec(v_a_2182_);
                    crate::leanh::lean_dec_ref(v_trivialType_2172_);
                    v___x_2253_ = crate::leanh::lean_box(0);
                    v___x_2254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
                    return v___x_2254_;
                }
            }
            3 => {
                v___x_2187_ = crate::leanh::lean_box(0);
                if v_isShared_2185_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2184_, 0, v___x_2187_);
                    v___x_2189_ = v___x_2184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
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
                crate::leanh::lean_dec(v_a_2199_);
                if v___x_2203_ == 0 {
                    crate::leanh::lean_del_object(v___x_2201_);
                    crate::leanh::lean_inc(v_head_2196_);
                    v___x_2204_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_getRelevantCtorFields(v_head_2196_, v_trivialType_2172_, v_a_2174_, v_a_2175_);
                    if crate::leanh::lean_obj_tag(v___x_2204_) == 0 {
                        v_a_2205_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
                        crate::leanh::lean_inc(v_a_2205_);
                        crate::leanh::lean_dec_ref_known(v___x_2204_, 1);
                        v___x_2206_ = lean_array_get_size(v_a_2205_);
                        v___x_2207_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2208_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache___closed__0;
                        v___x_2209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(v___x_2206_, v_val_2191_, v_head_2196_, v_a_2205_, v___x_2203_, v___x_2207_, v___x_2208_);
                        crate::leanh::lean_dec(v_a_2205_);
                        crate::leanh::lean_dec_ref(v_val_2191_);
                        if crate::leanh::lean_obj_tag(v___x_2209_) == 0 {
                            v_a_2210_ = crate::leanh::lean_ctor_get(v___x_2209_, 0);
                            v_isSharedCheck_2223_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2209_)) as u8;
                            if v_isSharedCheck_2223_ == 0 {
                                v___x_2212_ = v___x_2209_;
                                v_isShared_2213_ = v_isSharedCheck_2223_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2210_);
                                crate::leanh::lean_dec(v___x_2209_);
                                v___x_2212_ = crate::leanh::lean_box(0);
                                v_isShared_2213_ = v_isSharedCheck_2223_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_2224_ = crate::leanh::lean_ctor_get(v___x_2209_, 0);
                            v_isSharedCheck_2231_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2209_)) as u8;
                            if v_isSharedCheck_2231_ == 0 {
                                v___x_2226_ = v___x_2209_;
                                v_isShared_2227_ = v_isSharedCheck_2231_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2224_);
                                crate::leanh::lean_dec(v___x_2209_);
                                v___x_2226_ = crate::leanh::lean_box(0);
                                v_isShared_2227_ = v_isSharedCheck_2231_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_head_2196_);
                        crate::leanh::lean_dec_ref(v_val_2191_);
                        v_a_2232_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
                        v_isSharedCheck_2239_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2204_)) as u8;
                        if v_isSharedCheck_2239_ == 0 {
                            v___x_2234_ = v___x_2204_;
                            v_isShared_2235_ = v_isSharedCheck_2239_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2232_);
                            crate::leanh::lean_dec(v___x_2204_);
                            v___x_2234_ = crate::leanh::lean_box(0);
                            v_isShared_2235_ = v_isSharedCheck_2239_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_head_2196_);
                    crate::leanh::lean_dec_ref(v_val_2191_);
                    crate::leanh::lean_dec_ref(v_trivialType_2172_);
                    v___x_2240_ = crate::leanh::lean_box(0);
                    if v_isShared_2202_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2240_);
                        v___x_2242_ = v___x_2201_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
                        v___x_2242_ = v_reuseFailAlloc_2243_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_2214_ = crate::leanh::lean_ctor_get(v_a_2210_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2214_) == 0 {
                    v_snd_2215_ = crate::leanh::lean_ctor_get(v_a_2210_, 1);
                    crate::leanh::lean_inc(v_snd_2215_);
                    crate::leanh::lean_dec(v_a_2210_);
                    if v_isShared_2213_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2212_, 0, v_snd_2215_);
                        v___x_2217_ = v___x_2212_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_snd_2215_);
                        v___x_2217_ = v_reuseFailAlloc_2218_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2214_);
                    crate::leanh::lean_dec(v_a_2210_);
                    v_val_2219_ = crate::leanh::lean_ctor_get(v_fst_2214_, 0);
                    crate::leanh::lean_inc(v_val_2219_);
                    crate::leanh::lean_dec_ref_known(v_fst_2214_, 1);
                    if v_isShared_2213_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2212_, 0, v_val_2219_);
                        v___x_2221_ = v___x_2212_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_val_2219_);
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
                    v_reuseFailAlloc_2230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
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
                    v_reuseFailAlloc_2238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
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
                    v_reuseFailAlloc_2251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
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
                    v_reuseFailAlloc_2262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
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
    mut v_trivialType_2266_: *mut crate::leanh::LeanObject,
    mut v_declName_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
    mut v_a_2269_: *mut crate::leanh::LeanObject,
    mut v_a_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache(v_trivialType_2266_, v_declName_2267_, v_a_2268_, v_a_2269_);
    crate::leanh::lean_dec(v_a_2269_);
    crate::leanh::lean_dec_ref(v_a_2268_);
    return v_res_2271_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0(
    mut v_upperBound_2272_: *mut crate::leanh::LeanObject,
    mut v_val_2273_: *mut crate::leanh::LeanObject,
    mut v_head_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v___x_2276_: u8,
    mut v_inst_2277_: *mut crate::leanh::LeanObject,
    mut v_R_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_b_2280_: *mut crate::leanh::LeanObject,
    mut v_c_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___redArg(v_upperBound_2272_, v_val_2273_, v_head_2274_, v_a_2275_, v___x_2276_, v_a_2279_, v_b_2280_);
    return v___x_2285_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0___boxed(
    mut v_upperBound_2286_: *mut crate::leanh::LeanObject,
    mut v_val_2287_: *mut crate::leanh::LeanObject,
    mut v_head_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v___x_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
    mut v_R_2292_: *mut crate::leanh::LeanObject,
    mut v_a_2293_: *mut crate::leanh::LeanObject,
    mut v_b_2294_: *mut crate::leanh::LeanObject,
    mut v_c_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4525__boxed_2299_: u8 = 0;
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4525__boxed_2299_ = (crate::leanh::lean_unbox(v___x_2290_) as u8);
    v_res_2300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache_spec__0(v_upperBound_2286_, v_val_2287_, v_head_2288_, v_a_2289_, v___x_4525__boxed_2299_, v_inst_2291_, v_R_2292_, v_a_2293_, v_b_2294_, v_c_2295_, v___y_2296_, v___y_2297_);
    crate::leanh::lean_dec(v___y_2297_);
    crate::leanh::lean_dec_ref(v___y_2296_);
    crate::leanh::lean_dec_ref(v_a_2289_);
    crate::leanh::lean_dec_ref(v_val_2287_);
    crate::leanh::lean_dec(v_upperBound_2286_);
    return v_res_2300_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(
    mut v_x_2301_: *mut crate::leanh::LeanObject,
    mut v_x_2302_: *mut crate::leanh::LeanObject,
    mut v_x_2303_: *mut crate::leanh::LeanObject,
    mut v_x_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: u8 = 0;
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2305_ = crate::leanh::lean_ctor_get(v_x_2301_, 0);
                v_vs_2306_ = crate::leanh::lean_ctor_get(v_x_2301_, 1);
                v_isSharedCheck_2330_ = (!crate::leanh::lean_is_exclusive(v_x_2301_)) as u8;
                if v_isSharedCheck_2330_ == 0 {
                    v___x_2308_ = v_x_2301_;
                    v_isShared_2309_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2306_);
                    crate::leanh::lean_inc(v_ks_2305_);
                    crate::leanh::lean_dec(v_x_2301_);
                    v___x_2308_ = crate::leanh::lean_box(0);
                    v_isShared_2309_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2310_ = lean_array_get_size(v_ks_2305_);
                v___x_2311_ = lean_nat_dec_lt(v_x_2302_, v___x_2310_);
                if v___x_2311_ == 0 {
                    crate::leanh::lean_dec(v_x_2302_);
                    v___x_2312_ = lean_array_push(v_ks_2305_, v_x_2303_);
                    v___x_2313_ = lean_array_push(v_vs_2306_, v_x_2304_);
                    if v_isShared_2309_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2308_, 1, v___x_2313_);
                        crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2312_);
                        v___x_2315_ = v___x_2308_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2316_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2313_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_ks_2305_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_vs_2306_);
                            v___x_2320_ = v_reuseFailAlloc_2324_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2325_ = lean_array_fset(v_ks_2305_, v_x_2302_, v_x_2303_);
                        v___x_2326_ = lean_array_fset(v_vs_2306_, v_x_2302_, v_x_2304_);
                        crate::leanh::lean_dec(v_x_2302_);
                        if v_isShared_2309_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2308_, 1, v___x_2326_);
                            crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2325_);
                            v___x_2328_ = v___x_2308_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2329_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2325_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2326_);
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
                v___x_2321_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2322_ = lean_nat_add(v_x_2302_, v___x_2321_);
                crate::leanh::lean_dec(v_x_2302_);
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
    mut v_n_2331_: *mut crate::leanh::LeanObject,
    mut v_k_2332_: *mut crate::leanh::LeanObject,
    mut v_v_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_n_2331_, v___x_2334_, v_k_2332_, v_v_2333_);
    return v___x_2335_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: u64 = 0;
    v___x_2336_ = crate::leanh::lean_unsigned_to_nat(1723);
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
    v___x_2342_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__0);
    v___x_2343_ = lean_usize_sub(v___x_2342_, v___x_2341_);
    return v___x_2343_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2344_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_x_2345_: *mut crate::leanh::LeanObject,
    mut v_x_2346_: usize,
    mut v_x_2347_: usize,
    mut v_x_2348_: *mut crate::leanh::LeanObject,
    mut v_x_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    let mut v_j_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v_v_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_node_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v___x_2386_: usize = 0;
    let mut v___x_2387_: usize = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_unused_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: u8 = 0;
    let mut v_ks_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: usize = 0;
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: u8 = 0;
    let mut v_reuseFailAlloc_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2345_) == 0 {
                    v_es_2350_ = crate::leanh::lean_ctor_get(v_x_2345_, 0);
                    v___x_2351_ = 5usize;
                    v___x_2352_ = 1usize;
                    v___x_2353_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_2354_ = lean_usize_land(v_x_2346_, v___x_2353_);
                    v_j_2355_ = lean_usize_to_nat(v___x_2354_);
                    v___x_2356_ = lean_array_get_size(v_es_2350_);
                    v___x_2357_ = lean_nat_dec_lt(v_j_2355_, v___x_2356_);
                    if v___x_2357_ == 0 {
                        crate::leanh::lean_dec(v_j_2355_);
                        crate::leanh::lean_dec(v_x_2349_);
                        crate::leanh::lean_dec(v_x_2348_);
                        return v_x_2345_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2350_);
                        v_isSharedCheck_2394_ = (!crate::leanh::lean_is_exclusive(v_x_2345_)) as u8;
                        if v_isSharedCheck_2394_ == 0 {
                            v_unused_2395_ = crate::leanh::lean_ctor_get(v_x_2345_, 0);
                            crate::leanh::lean_dec(v_unused_2395_);
                            v___x_2359_ = v_x_2345_;
                            v_isShared_2360_ = v_isSharedCheck_2394_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2345_);
                            v___x_2359_ = crate::leanh::lean_box(0);
                            v_isShared_2360_ = v_isSharedCheck_2394_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2396_ = crate::leanh::lean_ctor_get(v_x_2345_, 0);
                    v_vs_2397_ = crate::leanh::lean_ctor_get(v_x_2345_, 1);
                    v_isSharedCheck_2417_ = (!crate::leanh::lean_is_exclusive(v_x_2345_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2399_ = v_x_2345_;
                        v_isShared_2400_ = v_isSharedCheck_2417_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2397_);
                        crate::leanh::lean_inc(v_ks_2396_);
                        crate::leanh::lean_dec(v_x_2345_);
                        v___x_2399_ = crate::leanh::lean_box(0);
                        v_isShared_2400_ = v_isSharedCheck_2417_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2361_ = lean_array_fget(v_es_2350_, v_j_2355_);
                v___x_2362_ = crate::leanh::lean_box(0);
                v_xs_x27_2363_ = lean_array_fset(v_es_2350_, v_j_2355_, v___x_2362_);
                match crate::leanh::lean_obj_tag(v_v_2361_) {
                    0 => {
                        v_key_2370_ = crate::leanh::lean_ctor_get(v_v_2361_, 0);
                        v_val_2371_ = crate::leanh::lean_ctor_get(v_v_2361_, 1);
                        v_isSharedCheck_2381_ = (!crate::leanh::lean_is_exclusive(v_v_2361_)) as u8;
                        if v_isSharedCheck_2381_ == 0 {
                            v___x_2373_ = v_v_2361_;
                            v_isShared_2374_ = v_isSharedCheck_2381_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2371_);
                            crate::leanh::lean_inc(v_key_2370_);
                            crate::leanh::lean_dec(v_v_2361_);
                            v___x_2373_ = crate::leanh::lean_box(0);
                            v_isShared_2374_ = v_isSharedCheck_2381_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2382_ = crate::leanh::lean_ctor_get(v_v_2361_, 0);
                        v_isSharedCheck_2392_ = (!crate::leanh::lean_is_exclusive(v_v_2361_)) as u8;
                        if v_isSharedCheck_2392_ == 0 {
                            v___x_2384_ = v_v_2361_;
                            v_isShared_2385_ = v_isSharedCheck_2392_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2382_);
                            crate::leanh::lean_dec(v_v_2361_);
                            v___x_2384_ = crate::leanh::lean_box(0);
                            v_isShared_2385_ = v_isSharedCheck_2392_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2393_, 0, v_x_2348_);
                        crate::leanh::lean_ctor_set(v___x_2393_, 1, v_x_2349_);
                        v___y_2365_ = v___x_2393_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2366_ = lean_array_fset(v_xs_x27_2363_, v_j_2355_, v___y_2365_);
                crate::leanh::lean_dec(v_j_2355_);
                if v_isShared_2360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2359_, 0, v___x_2366_);
                    v___x_2368_ = v___x_2359_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
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
                    crate::leanh::lean_del_object(v___x_2373_);
                    v___x_2376_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2370_,
                        v_val_2371_,
                        v_x_2348_,
                        v_x_2349_,
                    );
                    v___x_2377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2376_);
                    v___y_2365_ = v___x_2377_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2371_);
                    crate::leanh::lean_dec(v_key_2370_);
                    if v_isShared_2374_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2373_, 1, v_x_2349_);
                        crate::leanh::lean_ctor_set(v___x_2373_, 0, v_x_2348_);
                        v___x_2379_ = v___x_2373_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_x_2348_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_x_2349_);
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
                    crate::leanh::lean_ctor_set(v___x_2384_, 0, v___x_2388_);
                    v___x_2390_ = v___x_2384_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
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
                    v_reuseFailAlloc_2416_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_ks_2396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_vs_2397_);
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
                    v___x_2414_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
                    crate::leanh::lean_dec(v___x_2413_);
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
                    v_ks_2406_ = crate::leanh::lean_ctor_get(v_newNode_2403_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2406_);
                    v_vs_2407_ = crate::leanh::lean_ctor_get(v_newNode_2403_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2407_);
                    crate::leanh::lean_dec_ref(v_newNode_2403_);
                    v___x_2408_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__2);
                    v___x_2410_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(v_x_2347_, v_ks_2406_, v_vs_2407_, v___x_2408_, v___x_2409_);
                    crate::leanh::lean_dec_ref(v_vs_2407_);
                    crate::leanh::lean_dec_ref(v_ks_2406_);
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
    mut v_keys_2419_: *mut crate::leanh::LeanObject,
    mut v_vals_2420_: *mut crate::leanh::LeanObject,
    mut v_i_2421_: *mut crate::leanh::LeanObject,
    mut v_entries_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v_k_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: u64 = 0;
    let mut v_h_2429_: usize = 0;
    let mut v___x_2430_: usize = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: usize = 0;
    let mut v___x_2433_: usize = 0;
    let mut v___x_2434_: usize = 0;
    let mut v_h_2435_: usize = 0;
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u64 = 0;
    let mut v_hash_2440_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2423_ = lean_array_get_size(v_keys_2419_);
                v___x_2424_ = lean_nat_dec_lt(v_i_2421_, v___x_2423_);
                if v___x_2424_ == 0 {
                    crate::leanh::lean_dec(v_i_2421_);
                    return v_entries_2422_;
                } else {
                    v_k_2425_ = lean_array_fget_borrowed(v_keys_2419_, v_i_2421_);
                    v_v_2426_ = lean_array_fget_borrowed(v_vals_2420_, v_i_2421_);
                    if crate::leanh::lean_obj_tag(v_k_2425_) == 0 {
                        v___x_2439_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
                        v___y_2428_ = v___x_2439_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2440_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_2425_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
                v___x_2431_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2432_ = 1usize;
                v___x_2433_ = lean_usize_sub(v_depth_2418_, v___x_2432_);
                v___x_2434_ = lean_usize_mul(v___x_2430_, v___x_2433_);
                v_h_2435_ = lean_usize_shift_right(v_h_2429_, v___x_2434_);
                v___x_2436_ = lean_nat_add(v_i_2421_, v___x_2431_);
                crate::leanh::lean_dec(v_i_2421_);
                crate::leanh::lean_inc(v_v_2426_);
                crate::leanh::lean_inc(v_k_2425_);
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
    mut v_depth_2441_: *mut crate::leanh::LeanObject,
    mut v_keys_2442_: *mut crate::leanh::LeanObject,
    mut v_vals_2443_: *mut crate::leanh::LeanObject,
    mut v_i_2444_: *mut crate::leanh::LeanObject,
    mut v_entries_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2446_: usize = 0;
    let mut v_res_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2446_ = crate::leanh::lean_unbox_usize(v_depth_2441_);
    crate::leanh::lean_dec(v_depth_2441_);
    v_res_2447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(v_depth_boxed_2446_, v_keys_2442_, v_vals_2443_, v_i_2444_, v_entries_2445_);
    crate::leanh::lean_dec_ref(v_vals_2443_);
    crate::leanh::lean_dec_ref(v_keys_2442_);
    return v_res_2447_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_x_2448_: *mut crate::leanh::LeanObject,
    mut v_x_2449_: *mut crate::leanh::LeanObject,
    mut v_x_2450_: *mut crate::leanh::LeanObject,
    mut v_x_2451_: *mut crate::leanh::LeanObject,
    mut v_x_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_987__boxed_2453_: usize = 0;
    let mut v_x_988__boxed_2454_: usize = 0;
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_987__boxed_2453_ = crate::leanh::lean_unbox_usize(v_x_2449_);
    crate::leanh::lean_dec(v_x_2449_);
    v_x_988__boxed_2454_ = crate::leanh::lean_unbox_usize(v_x_2450_);
    crate::leanh::lean_dec(v_x_2450_);
    v_res_2455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_x_2448_, v_x_987__boxed_2453_, v_x_988__boxed_2454_, v_x_2451_, v_x_2452_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2___redArg(
    mut v_x_2456_: *mut crate::leanh::LeanObject,
    mut v_x_2457_: *mut crate::leanh::LeanObject,
    mut v_x_2458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2460_: u64 = 0;
    let mut v___x_2461_: usize = 0;
    let mut v___x_2462_: usize = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u64 = 0;
    let mut v_hash_2465_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2457_) == 0 {
                    v___x_2464_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
                    v___y_2460_ = v___x_2464_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2465_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2457_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_b_2467_: *mut crate::leanh::LeanObject,
    mut v_x_2468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2469_ = crate::leanh::lean_ctor_get(v_x_2468_, 0);
                v_snd_2470_ = crate::leanh::lean_ctor_get(v_x_2468_, 1);
                v_isSharedCheck_2479_ = (!crate::leanh::lean_is_exclusive(v_x_2468_)) as u8;
                if v_isSharedCheck_2479_ == 0 {
                    v___x_2472_ = v_x_2468_;
                    v_isShared_2473_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2470_);
                    crate::leanh::lean_inc(v_fst_2469_);
                    crate::leanh::lean_dec(v_x_2468_);
                    v___x_2472_ = crate::leanh::lean_box(0);
                    v_isShared_2473_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2466_);
                v___x_2474_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2474_, 0, v_a_2466_);
                crate::leanh::lean_ctor_set(v___x_2474_, 1, v_fst_2469_);
                v___x_2475_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2___redArg(v_snd_2470_, v_a_2466_, v_b_2467_);
                if v_isShared_2473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2472_, 1, v___x_2475_);
                    crate::leanh::lean_ctor_set(v___x_2472_, 0, v___x_2474_);
                    v___x_2477_ = v___x_2472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2475_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__0);
    v___x_2482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2481_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__1);
    v___x_2484_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    crate::leanh::lean_ctor_set(v___x_2484_, 1, v___x_2483_);
    return v___x_2484_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(
    mut v_ext_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_b_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v_asyncMode_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut v_unused_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2490_ = lean_st_ref_take(v_a_2488_);
                v_env_2491_ = crate::leanh::lean_ctor_get(v___x_2490_, 0);
                v_nextMacroScope_2492_ = crate::leanh::lean_ctor_get(v___x_2490_, 1);
                v_ngen_2493_ = crate::leanh::lean_ctor_get(v___x_2490_, 2);
                v_auxDeclNGen_2494_ = crate::leanh::lean_ctor_get(v___x_2490_, 3);
                v_traceState_2495_ = crate::leanh::lean_ctor_get(v___x_2490_, 4);
                v_messages_2496_ = crate::leanh::lean_ctor_get(v___x_2490_, 6);
                v_infoState_2497_ = crate::leanh::lean_ctor_get(v___x_2490_, 7);
                v_snapshotTasks_2498_ = crate::leanh::lean_ctor_get(v___x_2490_, 8);
                v_isSharedCheck_2513_ = (!crate::leanh::lean_is_exclusive(v___x_2490_)) as u8;
                if v_isSharedCheck_2513_ == 0 {
                    v_unused_2514_ = crate::leanh::lean_ctor_get(v___x_2490_, 5);
                    crate::leanh::lean_dec(v_unused_2514_);
                    v___x_2500_ = v___x_2490_;
                    v_isShared_2501_ = v_isSharedCheck_2513_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2498_);
                    crate::leanh::lean_inc(v_infoState_2497_);
                    crate::leanh::lean_inc(v_messages_2496_);
                    crate::leanh::lean_inc(v_traceState_2495_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2494_);
                    crate::leanh::lean_inc(v_ngen_2493_);
                    crate::leanh::lean_inc(v_nextMacroScope_2492_);
                    crate::leanh::lean_inc(v_env_2491_);
                    crate::leanh::lean_dec(v___x_2490_);
                    v___x_2500_ = crate::leanh::lean_box(0);
                    v_isShared_2501_ = v_isSharedCheck_2513_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_2502_ = crate::leanh::lean_ctor_get(v_ext_2485_, 2);
                crate::leanh::lean_inc(v_asyncMode_2502_);
                v___f_2503_ = crate::leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                crate::leanh::lean_closure_set(v___f_2503_, 0, v_a_2486_);
                crate::leanh::lean_closure_set(v___f_2503_, 1, v_b_2487_);
                v___x_2504_ = crate::leanh::lean_box(0);
                v___x_2505_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_2485_,
                    v_env_2491_,
                    v___f_2503_,
                    v_asyncMode_2502_,
                    v___x_2504_,
                );
                crate::leanh::lean_dec(v_asyncMode_2502_);
                v___x_2506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___closed__2);
                if v_isShared_2501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2500_, 5, v___x_2506_);
                    crate::leanh::lean_ctor_set(v___x_2500_, 0, v___x_2505_);
                    v___x_2508_ = v___x_2500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_nextMacroScope_2492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_ngen_2493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_auxDeclNGen_2494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_traceState_2495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 5, v___x_2506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_messages_2496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 7, v_infoState_2497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 8, v_snapshotTasks_2498_);
                    v___x_2508_ = v_reuseFailAlloc_2512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2509_ = lean_st_ref_set(v_a_2488_, v___x_2508_);
                v___x_2510_ = crate::leanh::lean_box(0);
                v___x_2511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg___boxed(
    mut v_ext_2515_: *mut crate::leanh::LeanObject,
    mut v_a_2516_: *mut crate::leanh::LeanObject,
    mut v_b_2517_: *mut crate::leanh::LeanObject,
    mut v_a_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2520_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(v_ext_2515_, v_a_2516_, v_b_2517_, v_a_2518_);
    crate::leanh::lean_dec(v_a_2518_);
    return v_res_2520_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_2521_: *mut crate::leanh::LeanObject,
    mut v_vals_2522_: *mut crate::leanh::LeanObject,
    mut v_i_2523_: *mut crate::leanh::LeanObject,
    mut v_k_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2525_ = lean_array_get_size(v_keys_2521_);
                v___x_2526_ = lean_nat_dec_lt(v_i_2523_, v___x_2525_);
                if v___x_2526_ == 0 {
                    crate::leanh::lean_dec(v_i_2523_);
                    v___x_2527_ = crate::leanh::lean_box(0);
                    return v___x_2527_;
                } else {
                    v_k_x27_2528_ = lean_array_fget_borrowed(v_keys_2521_, v_i_2523_);
                    v___x_2529_ = lean_name_eq(v_k_2524_, v_k_x27_2528_);
                    if v___x_2529_ == 0 {
                        v___x_2530_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2531_ = lean_nat_add(v_i_2523_, v___x_2530_);
                        crate::leanh::lean_dec(v_i_2523_);
                        v_i_2523_ = v___x_2531_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2533_ = lean_array_fget_borrowed(v_vals_2522_, v_i_2523_);
                        crate::leanh::lean_dec(v_i_2523_);
                        crate::leanh::lean_inc(v___x_2533_);
                        v___x_2534_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2534_, 0, v___x_2533_);
                        return v___x_2534_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_2535_: *mut crate::leanh::LeanObject,
    mut v_vals_2536_: *mut crate::leanh::LeanObject,
    mut v_i_2537_: *mut crate::leanh::LeanObject,
    mut v_k_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2535_, v_vals_2536_, v_i_2537_, v_k_2538_);
    crate::leanh::lean_dec(v_k_2538_);
    crate::leanh::lean_dec_ref(v_vals_2536_);
    crate::leanh::lean_dec_ref(v_keys_2535_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_2540_: *mut crate::leanh::LeanObject,
    mut v_x_2541_: usize,
    mut v_x_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: usize = 0;
    let mut v___x_2546_: usize = 0;
    let mut v___x_2547_: usize = 0;
    let mut v_j_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2540_) == 0 {
                    v_es_2543_ = crate::leanh::lean_ctor_get(v_x_2540_, 0);
                    v___x_2544_ = crate::leanh::lean_box(2);
                    v___x_2545_ = 5usize;
                    v___x_2546_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_2547_ = lean_usize_land(v_x_2541_, v___x_2546_);
                    v_j_2548_ = lean_usize_to_nat(v___x_2547_);
                    v___x_2549_ = lean_array_get_borrowed(v___x_2544_, v_es_2543_, v_j_2548_);
                    crate::leanh::lean_dec(v_j_2548_);
                    match crate::leanh::lean_obj_tag(v___x_2549_) {
                        0 => {
                            v_key_2550_ = crate::leanh::lean_ctor_get(v___x_2549_, 0);
                            v_val_2551_ = crate::leanh::lean_ctor_get(v___x_2549_, 1);
                            v___x_2552_ = lean_name_eq(v_x_2542_, v_key_2550_);
                            if v___x_2552_ == 0 {
                                v___x_2553_ = crate::leanh::lean_box(0);
                                return v___x_2553_;
                            } else {
                                crate::leanh::lean_inc(v_val_2551_);
                                v___x_2554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2554_, 0, v_val_2551_);
                                return v___x_2554_;
                            }
                        }
                        1 => {
                            v_node_2555_ = crate::leanh::lean_ctor_get(v___x_2549_, 0);
                            v___x_2556_ = lean_usize_shift_right(v_x_2541_, v___x_2545_);
                            v_x_2540_ = v_node_2555_;
                            v_x_2541_ = v___x_2556_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2558_ = crate::leanh::lean_box(0);
                            return v___x_2558_;
                        }
                    }
                } else {
                    v_ks_2559_ = crate::leanh::lean_ctor_get(v_x_2540_, 0);
                    v_vs_2560_ = crate::leanh::lean_ctor_get(v_x_2540_, 1);
                    v___x_2561_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2562_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2559_, v_vs_2560_, v___x_2561_, v_x_2542_);
                    return v___x_2562_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2563_: *mut crate::leanh::LeanObject,
    mut v_x_2564_: *mut crate::leanh::LeanObject,
    mut v_x_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1274__boxed_2566_: usize = 0;
    let mut v_res_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1274__boxed_2566_ = crate::leanh::lean_unbox_usize(v_x_2564_);
    crate::leanh::lean_dec(v_x_2564_);
    v_res_2567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(v_x_2563_, v_x_1274__boxed_2566_, v_x_2565_);
    crate::leanh::lean_dec(v_x_2565_);
    crate::leanh::lean_dec_ref(v_x_2563_);
    return v_res_2567_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(
    mut v_x_2568_: *mut crate::leanh::LeanObject,
    mut v_x_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2571_: u64 = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u64 = 0;
    let mut v_hash_2575_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2569_) == 0 {
                    v___x_2574_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
                    v___y_2571_ = v___x_2574_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2575_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2569_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
    mut v_x_2576_: *mut crate::leanh::LeanObject,
    mut v_x_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2578_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(v_x_2576_, v_x_2577_);
    crate::leanh::lean_dec(v_x_2577_);
    crate::leanh::lean_dec_ref(v_x_2576_);
    return v_res_2578_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2581_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__1;
    v___x_2582_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__0;
    v___x_2583_ = l_Lean_PersistentHashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2582_,
        v___x_2581_,
    );
    return v___x_2583_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__2);
    v___x_2585_ = crate::leanh::lean_box(0);
    v___x_2586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2586_, 0, v___x_2585_);
    crate::leanh::lean_ctor_set(v___x_2586_, 1, v___x_2584_);
    return v___x_2586_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(
    mut v_ext_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = lean_st_ref_get(v_a_2589_);
    v_env_2592_ = crate::leanh::lean_ctor_get(v___x_2591_, 0);
    crate::leanh::lean_inc_ref(v_env_2592_);
    crate::leanh::lean_dec(v___x_2591_);
    v_asyncMode_2593_ = crate::leanh::lean_ctor_get(v_ext_2587_, 2);
    v___x_2594_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___closed__3);
    v___x_2595_ = crate::leanh::lean_box(0);
    v___x_2596_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_2594_,
        v_ext_2587_,
        v_env_2592_,
        v_asyncMode_2593_,
        v___x_2595_,
    );
    v_snd_2597_ = crate::leanh::lean_ctor_get(v___x_2596_, 1);
    crate::leanh::lean_inc(v_snd_2597_);
    crate::leanh::lean_dec(v___x_2596_);
    v___x_2598_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(v_snd_2597_, v_a_2588_);
    crate::leanh::lean_dec(v_snd_2597_);
    v___x_2599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2599_, 0, v___x_2598_);
    return v___x_2599_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg___boxed(
    mut v_ext_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_a_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(v_ext_2600_, v_a_2601_, v_a_2602_);
    crate::leanh::lean_dec(v_a_2602_);
    crate::leanh::lean_dec(v_a_2601_);
    crate::leanh::lean_dec_ref(v_ext_2600_);
    return v_res_2604_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(
    mut v_cacheExt_2605_: *mut crate::leanh::LeanObject,
    mut v_trivialType_2606_: *mut crate::leanh::LeanObject,
    mut v_declName_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_unused_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2611_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(v_cacheExt_2605_, v_declName_2607_, v_a_2609_);
                v_a_2612_ = crate::leanh::lean_ctor_get(v___x_2611_, 0);
                v_isSharedCheck_2631_ = (!crate::leanh::lean_is_exclusive(v___x_2611_)) as u8;
                if v_isSharedCheck_2631_ == 0 {
                    v___x_2614_ = v___x_2611_;
                    v_isShared_2615_ = v_isSharedCheck_2631_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2612_);
                    crate::leanh::lean_dec(v___x_2611_);
                    v___x_2614_ = crate::leanh::lean_box(0);
                    v_isShared_2615_ = v_isSharedCheck_2631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2612_) == 0 {
                    crate::leanh::lean_del_object(v___x_2614_);
                    crate::leanh::lean_inc(v_declName_2607_);
                    v___x_2616_ = l___private_Lean_Compiler_LCNF_Irrelevant_0__Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_fillCache(v_trivialType_2606_, v_declName_2607_, v_a_2608_, v_a_2609_);
                    if crate::leanh::lean_obj_tag(v___x_2616_) == 0 {
                        v_a_2617_ = crate::leanh::lean_ctor_get(v___x_2616_, 0);
                        crate::leanh::lean_inc_n(v_a_2617_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2616_, 1);
                        v___x_2618_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(v_cacheExt_2605_, v_declName_2607_, v_a_2617_, v_a_2609_);
                        v_isSharedCheck_2625_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2618_)) as u8;
                        if v_isSharedCheck_2625_ == 0 {
                            v_unused_2626_ = crate::leanh::lean_ctor_get(v___x_2618_, 0);
                            crate::leanh::lean_dec(v_unused_2626_);
                            v___x_2620_ = v___x_2618_;
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2618_);
                            v___x_2620_ = crate::leanh::lean_box(0);
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_2607_);
                        crate::leanh::lean_dec_ref(v_cacheExt_2605_);
                        return v___x_2616_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2607_);
                    crate::leanh::lean_dec_ref(v_trivialType_2606_);
                    crate::leanh::lean_dec_ref(v_cacheExt_2605_);
                    v_val_2627_ = crate::leanh::lean_ctor_get(v_a_2612_, 0);
                    crate::leanh::lean_inc(v_val_2627_);
                    crate::leanh::lean_dec_ref_known(v_a_2612_, 1);
                    if v_isShared_2615_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2614_, 0, v_val_2627_);
                        v___x_2629_ = v___x_2614_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_val_2627_);
                        v___x_2629_ = v_reuseFailAlloc_2630_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2621_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2620_, 0, v_a_2617_);
                    v___x_2623_ = v___x_2620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2617_);
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
    mut v_cacheExt_2632_: *mut crate::leanh::LeanObject,
    mut v_trivialType_2633_: *mut crate::leanh::LeanObject,
    mut v_declName_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(
        v_cacheExt_2632_,
        v_trivialType_2633_,
        v_declName_2634_,
        v_a_2635_,
        v_a_2636_,
    );
    crate::leanh::lean_dec(v_a_2636_);
    crate::leanh::lean_dec_ref(v_a_2635_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0(
    mut v_ext_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___redArg(v_ext_2639_, v_a_2640_, v_a_2642_);
    return v___x_2644_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0___boxed(
    mut v_ext_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
    mut v_a_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2650_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0(v_ext_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
    crate::leanh::lean_dec(v_a_2648_);
    crate::leanh::lean_dec_ref(v_a_2647_);
    crate::leanh::lean_dec(v_a_2646_);
    crate::leanh::lean_dec_ref(v_ext_2645_);
    return v_res_2650_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1(
    mut v_ext_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_b_2653_: *mut crate::leanh::LeanObject,
    mut v_a_2654_: *mut crate::leanh::LeanObject,
    mut v_a_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2657_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___redArg(v_ext_2651_, v_a_2652_, v_b_2653_, v_a_2655_);
    return v___x_2657_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1___boxed(
    mut v_ext_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_b_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
    mut v_a_2662_: *mut crate::leanh::LeanObject,
    mut v_a_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1(v_ext_2658_, v_a_2659_, v_b_2660_, v_a_2661_, v_a_2662_);
    crate::leanh::lean_dec(v_a_2662_);
    crate::leanh::lean_dec_ref(v_a_2661_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0(
    mut v_00_u03b2_2665_: *mut crate::leanh::LeanObject,
    mut v_x_2666_: *mut crate::leanh::LeanObject,
    mut v_x_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___redArg(v_x_2666_, v_x_2667_);
    return v___x_2668_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2669_: *mut crate::leanh::LeanObject,
    mut v_x_2670_: *mut crate::leanh::LeanObject,
    mut v_x_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0(v_00_u03b2_2669_, v_x_2670_, v_x_2671_);
    crate::leanh::lean_dec(v_x_2671_);
    crate::leanh::lean_dec_ref(v_x_2670_);
    return v_res_2672_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2(
    mut v_00_u03b2_2673_: *mut crate::leanh::LeanObject,
    mut v_x_2674_: *mut crate::leanh::LeanObject,
    mut v_x_2675_: *mut crate::leanh::LeanObject,
    mut v_x_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2___redArg(v_x_2674_, v_x_2675_, v_x_2676_);
    return v___x_2677_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2678_: *mut crate::leanh::LeanObject,
    mut v_x_2679_: *mut crate::leanh::LeanObject,
    mut v_x_2680_: usize,
    mut v_x_2681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___redArg(v_x_2679_, v_x_2680_, v_x_2681_);
    return v___x_2682_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2683_: *mut crate::leanh::LeanObject,
    mut v_x_2684_: *mut crate::leanh::LeanObject,
    mut v_x_2685_: *mut crate::leanh::LeanObject,
    mut v_x_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1456__boxed_2687_: usize = 0;
    let mut v_res_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1456__boxed_2687_ = crate::leanh::lean_unbox_usize(v_x_2685_);
    crate::leanh::lean_dec(v_x_2685_);
    v_res_2688_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2683_, v_x_2684_, v_x_1456__boxed_2687_, v_x_2686_);
    crate::leanh::lean_dec(v_x_2686_);
    crate::leanh::lean_dec_ref(v_x_2684_);
    return v_res_2688_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2689_: *mut crate::leanh::LeanObject,
    mut v_x_2690_: *mut crate::leanh::LeanObject,
    mut v_x_2691_: usize,
    mut v_x_2692_: usize,
    mut v_x_2693_: *mut crate::leanh::LeanObject,
    mut v_x_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___redArg(v_x_2690_, v_x_2691_, v_x_2692_, v_x_2693_, v_x_2694_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_2696_: *mut crate::leanh::LeanObject,
    mut v_x_2697_: *mut crate::leanh::LeanObject,
    mut v_x_2698_: *mut crate::leanh::LeanObject,
    mut v_x_2699_: *mut crate::leanh::LeanObject,
    mut v_x_2700_: *mut crate::leanh::LeanObject,
    mut v_x_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1467__boxed_2702_: usize = 0;
    let mut v_x_1468__boxed_2703_: usize = 0;
    let mut v_res_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1467__boxed_2702_ = crate::leanh::lean_unbox_usize(v_x_2698_);
    crate::leanh::lean_dec(v_x_2698_);
    v_x_1468__boxed_2703_ = crate::leanh::lean_unbox_usize(v_x_2699_);
    crate::leanh::lean_dec(v_x_2699_);
    v_res_2704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4(v_00_u03b2_2696_, v_x_2697_, v_x_1467__boxed_2702_, v_x_1468__boxed_2703_, v_x_2700_, v_x_2701_);
    return v_res_2704_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2705_: *mut crate::leanh::LeanObject,
    mut v_keys_2706_: *mut crate::leanh::LeanObject,
    mut v_vals_2707_: *mut crate::leanh::LeanObject,
    mut v_heq_2708_: *mut crate::leanh::LeanObject,
    mut v_i_2709_: *mut crate::leanh::LeanObject,
    mut v_k_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2711_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2706_, v_vals_2707_, v_i_2709_, v_k_2710_);
    return v___x_2711_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2712_: *mut crate::leanh::LeanObject,
    mut v_keys_2713_: *mut crate::leanh::LeanObject,
    mut v_vals_2714_: *mut crate::leanh::LeanObject,
    mut v_heq_2715_: *mut crate::leanh::LeanObject,
    mut v_i_2716_: *mut crate::leanh::LeanObject,
    mut v_k_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2712_, v_keys_2713_, v_vals_2714_, v_heq_2715_, v_i_2716_, v_k_2717_);
    crate::leanh::lean_dec(v_k_2717_);
    crate::leanh::lean_dec_ref(v_vals_2714_);
    crate::leanh::lean_dec_ref(v_keys_2713_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2719_: *mut crate::leanh::LeanObject,
    mut v_n_2720_: *mut crate::leanh::LeanObject,
    mut v_k_2721_: *mut crate::leanh::LeanObject,
    mut v_v_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6___redArg(v_n_2720_, v_k_2721_, v_v_2722_);
    return v___x_2723_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2724_: *mut crate::leanh::LeanObject,
    mut v_depth_2725_: usize,
    mut v_keys_2726_: *mut crate::leanh::LeanObject,
    mut v_vals_2727_: *mut crate::leanh::LeanObject,
    mut v_heq_2728_: *mut crate::leanh::LeanObject,
    mut v_i_2729_: *mut crate::leanh::LeanObject,
    mut v_entries_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___redArg(v_depth_2725_, v_keys_2726_, v_vals_2727_, v_i_2729_, v_entries_2730_);
    return v___x_2731_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_2732_: *mut crate::leanh::LeanObject,
    mut v_depth_2733_: *mut crate::leanh::LeanObject,
    mut v_keys_2734_: *mut crate::leanh::LeanObject,
    mut v_vals_2735_: *mut crate::leanh::LeanObject,
    mut v_heq_2736_: *mut crate::leanh::LeanObject,
    mut v_i_2737_: *mut crate::leanh::LeanObject,
    mut v_entries_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2739_: usize = 0;
    let mut v_res_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2739_ = crate::leanh::lean_unbox_usize(v_depth_2733_);
    crate::leanh::lean_dec(v_depth_2733_);
    v_res_2740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_2732_, v_depth_boxed_2739_, v_keys_2734_, v_vals_2735_, v_heq_2736_, v_i_2737_, v_entries_2738_);
    crate::leanh::lean_dec_ref(v_vals_2735_);
    crate::leanh::lean_dec_ref(v_keys_2734_);
    return v_res_2740_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2741_: *mut crate::leanh::LeanObject,
    mut v_x_2742_: *mut crate::leanh::LeanObject,
    mut v_x_2743_: *mut crate::leanh::LeanObject,
    mut v_x_2744_: *mut crate::leanh::LeanObject,
    mut v_x_2745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2746_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2742_, v_x_2743_, v_x_2744_, v_x_2745_);
    return v___x_2746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Irrelevant(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Irrelevant(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Irrelevant(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
}
