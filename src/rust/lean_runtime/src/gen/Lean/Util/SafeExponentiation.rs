// Lean compiler output
// Module: Lean.Util.SafeExponentiation
// Imports: Lean.CoreM
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::{
    initialize_Lean_CoreM, l_Lean_logMessageKind___redArg, runtime_initialize_Lean_CoreM,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 111, 110, 101, 110, 116, 105, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 0]};
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3987189949730487891 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13788463649086340923 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<300> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 300, m_capacity: 300, m_length: 299, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 118, 97, 108, 117, 101, 32, 102, 111, 114, 32, 119, 104, 105, 99, 104, 32, 101, 120, 112, 111, 110, 101, 110, 116, 105, 97, 116, 105, 111, 110, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 115, 32, 97, 114, 101, 32, 115, 97, 102, 101, 32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 46, 32, 87, 104, 101, 110, 32, 97, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116, 32, 105, 115, 32, 97, 32, 118, 97, 108, 117, 101, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104, 97, 110, 32, 116, 104, 105, 115, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 44, 32, 116, 104, 101, 32, 101, 120, 112, 111, 110, 101, 110, 116, 105, 97, 116, 105, 111, 110, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 98, 101, 32, 101, 118, 97, 108, 117, 97, 116, 101, 100, 44, 32, 97, 110, 100, 32, 97, 32, 119, 97, 114, 110, 105, 110, 103, 32, 119, 105, 108, 108, 32, 98, 101, 32, 108, 111, 103, 103, 101, 100, 46, 32, 84, 104, 105, 115, 32, 104, 101, 108, 112, 115, 32, 116, 111, 32, 112, 114, 101, 118, 101, 110, 116, 32, 116, 104, 101, 32, 115, 121, 115, 116, 101, 109, 32, 102, 114, 111, 109, 32, 98, 101, 99, 111, 109, 105, 110, 103, 32, 117, 110, 114, 101, 115, 112, 111, 110, 115, 105, 118, 101, 32, 100, 117, 101, 32, 116, 111, 32, 101, 120, 99, 101, 115, 115, 105, 118, 101, 108, 121, 32, 108, 97, 114, 103, 101, 32, 99, 111, 109, 112, 117, 116, 97, 116, 105, 111, 110, 115, 46, 0]};
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 256 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__3_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__5_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13408274642883822402 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__1_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,18219592033411212790 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_exponentiation_threshold: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkExponent___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [117, 110, 115, 97, 102, 101, 0],
    };
static mut l_Lean_checkExponent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkExponent___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_checkExponent___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_checkExponent___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1575876207306040598 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_checkExponent___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_checkExponent___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__0_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,35541827236266802 as *mut crate::leanh::LeanObject] };
static mut l_Lean_checkExponent___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkExponent___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkExponent___closed__2_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [101, 120, 112, 111, 110, 101, 110, 116, 32, 0],
    };
static mut l_Lean_checkExponent___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkExponent___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkExponent___closed__3_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            32, 101, 120, 99, 101, 101, 100, 115, 32, 116, 104, 101, 32, 116, 104, 114, 101, 115,
            104, 111, 108, 100, 32, 0,
        ],
    };
static mut l_Lean_checkExponent___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkExponent___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkExponent___closed__4_value: crate::leanh::LeanStringObject<63> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 63,
        m_capacity: 63,
        m_length: 62,
        m_data: [
            44, 32, 101, 120, 112, 111, 110, 101, 110, 116, 105, 97, 116, 105, 111, 110, 32, 111,
            112, 101, 114, 97, 116, 105, 111, 110, 32, 119, 97, 115, 32, 110, 111, 116, 32, 101,
            118, 97, 108, 117, 97, 116, 101, 100, 44, 32, 117, 115, 101, 32, 96, 115, 101, 116, 95,
            111, 112, 116, 105, 111, 110, 32, 0,
        ],
    };
static mut l_Lean_checkExponent___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkExponent___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_checkExponent___closed__5_value: crate::leanh::LeanStringObject<31> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 115, 101, 116, 32, 97, 32, 110, 101,
            119, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_checkExponent___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkExponent___closed__5_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(
    mut v_name_384_: *mut crate::leanh::LeanObject,
    mut v_decl_385_: *mut crate::leanh::LeanObject,
    mut v_ref_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_401_: u8 = 0;
    let mut v_unused_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_388_ = crate::leanh::lean_ctor_get(v_decl_385_, 0);
                v_descr_389_ = crate::leanh::lean_ctor_get(v_decl_385_, 1);
                v_deprecation_x3f_390_ = crate::leanh::lean_ctor_get(v_decl_385_, 2);
                crate::leanh::lean_inc(v_defValue_388_);
                v___x_391_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_391_, 0, v_defValue_388_);
                crate::leanh::lean_inc(v_deprecation_x3f_390_);
                crate::leanh::lean_inc_ref(v_descr_389_);
                crate::leanh::lean_inc_n(v_name_384_, 2);
                v___x_392_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_392_, 0, v_name_384_);
                crate::leanh::lean_ctor_set(v___x_392_, 1, v_ref_386_);
                crate::leanh::lean_ctor_set(v___x_392_, 2, v___x_391_);
                crate::leanh::lean_ctor_set(v___x_392_, 3, v_descr_389_);
                crate::leanh::lean_ctor_set(v___x_392_, 4, v_deprecation_x3f_390_);
                v___x_393_ = lean_register_option(v_name_384_, v___x_392_);
                if crate::leanh::lean_obj_tag(v___x_393_) == 0 {
                    v_isSharedCheck_401_ = (!crate::leanh::lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_401_ == 0 {
                        v_unused_402_ = crate::leanh::lean_ctor_get(v___x_393_, 0);
                        crate::leanh::lean_dec(v_unused_402_);
                        v___x_395_ = v___x_393_;
                        v_isShared_396_ = v_isSharedCheck_401_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_393_);
                        v___x_395_ = crate::leanh::lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_401_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_384_);
                    v_a_403_ = crate::leanh::lean_ctor_get(v___x_393_, 0);
                    v_isSharedCheck_410_ = (!crate::leanh::lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_410_ == 0 {
                        v___x_405_ = v___x_393_;
                        v_isShared_406_ = v_isSharedCheck_410_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_403_);
                        crate::leanh::lean_dec(v___x_393_);
                        v___x_405_ = crate::leanh::lean_box(0);
                        v_isShared_406_ = v_isSharedCheck_410_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_388_);
                v___x_397_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_397_, 0, v_name_384_);
                crate::leanh::lean_ctor_set(v___x_397_, 1, v_defValue_388_);
                if v_isShared_396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_395_, 0, v___x_397_);
                    v___x_399_ = v___x_395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
                    v___x_399_ = v_reuseFailAlloc_400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_399_;
            }
            3 => {
                if v_isShared_406_ == 0 {
                    v___x_408_ = v___x_405_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
                    v___x_408_ = v_reuseFailAlloc_409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_411_: *mut crate::leanh::LeanObject,
    mut v_decl_412_: *mut crate::leanh::LeanObject,
    mut v_ref_413_: *mut crate::leanh::LeanObject,
    mut v_a_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v_name_411_, v_decl_412_, v_ref_413_);
    crate::leanh::lean_dec_ref(v_decl_412_);
    return v_res_415_;
}
pub unsafe fn l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__2_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_;
    v___x_433_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__4_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_;
    v___x_434_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn___closed__6_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_;
    v___x_435_ = l_Lean_Option_register___at___00__private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4__spec__0(v___x_432_, v___x_433_, v___x_434_);
    return v___x_435_;
}
pub unsafe fn l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4____boxed(
    mut v_a_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_437_ = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
    return v_res_437_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_checkExponent_spec__0(
    mut v_opts_438_: *mut crate::leanh::LeanObject,
    mut v_opt_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_440_ = crate::leanh::lean_ctor_get(v_opt_439_, 0);
    v_defValue_441_ = crate::leanh::lean_ctor_get(v_opt_439_, 1);
    v_map_442_ = crate::leanh::lean_ctor_get(v_opts_438_, 0);
    v___x_443_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_442_,
            v_name_440_,
        );
    if crate::leanh::lean_obj_tag(v___x_443_) == 0 {
        crate::leanh::lean_inc(v_defValue_441_);
        return v_defValue_441_;
    } else {
        let mut v_val_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_444_ = crate::leanh::lean_ctor_get(v___x_443_, 0);
        crate::leanh::lean_inc(v_val_444_);
        crate::leanh::lean_dec_ref_known(v___x_443_, 1);
        if crate::leanh::lean_obj_tag(v_val_444_) == 3 {
            let mut v_v_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_445_ = crate::leanh::lean_ctor_get(v_val_444_, 0);
            crate::leanh::lean_inc(v_v_445_);
            crate::leanh::lean_dec_ref_known(v_val_444_, 1);
            return v_v_445_;
        } else {
            crate::leanh::lean_dec(v_val_444_);
            crate::leanh::lean_inc(v_defValue_441_);
            return v_defValue_441_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_checkExponent_spec__0___boxed(
    mut v_opts_446_: *mut crate::leanh::LeanObject,
    mut v_opt_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Lean_Option_get___at___00Lean_checkExponent_spec__0(v_opts_446_, v_opt_447_);
    crate::leanh::lean_dec_ref(v_opt_447_);
    crate::leanh::lean_dec_ref(v_opts_446_);
    return v_res_448_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(
    mut v_opts_449_: *mut crate::leanh::LeanObject,
    mut v_opt_450_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_451_ = crate::leanh::lean_ctor_get(v_opt_450_, 0);
    v_defValue_452_ = crate::leanh::lean_ctor_get(v_opt_450_, 1);
    v_map_453_ = crate::leanh::lean_ctor_get(v_opts_449_, 0);
    v___x_454_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_453_,
            v_name_451_,
        );
    if crate::leanh::lean_obj_tag(v___x_454_) == 0 {
        let mut v___x_455_: u8 = 0;
        v___x_455_ = (crate::leanh::lean_unbox(v_defValue_452_) as u8);
        return v___x_455_;
    } else {
        let mut v_val_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_456_ = crate::leanh::lean_ctor_get(v___x_454_, 0);
        crate::leanh::lean_inc(v_val_456_);
        crate::leanh::lean_dec_ref_known(v___x_454_, 1);
        if crate::leanh::lean_obj_tag(v_val_456_) == 1 {
            let mut v_v_457_: u8 = 0;
            v_v_457_ = crate::leanh::lean_ctor_get_uint8(v_val_456_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_456_, 0);
            return v_v_457_;
        } else {
            let mut v___x_458_: u8 = 0;
            crate::leanh::lean_dec(v_val_456_);
            v___x_458_ = (crate::leanh::lean_unbox(v_defValue_452_) as u8);
            return v___x_458_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_opts_459_: *mut crate::leanh::LeanObject,
    mut v_opt_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: u8 = 0;
    let mut v_r_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_opts_459_, v_opt_460_);
    crate::leanh::lean_dec_ref(v_opt_460_);
    crate::leanh::lean_dec_ref(v_opts_459_);
    v_r_462_ = crate::leanh::lean_box((v_res_461_) as usize);
    return v_r_462_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_463_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__0);
    v___x_465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_465_, 0, v___x_464_);
    return v___x_465_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
    v___x_467_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_468_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_468_, 0, v___x_467_);
    crate::leanh::lean_ctor_set(v___x_468_, 1, v___x_467_);
    crate::leanh::lean_ctor_set(v___x_468_, 2, v___x_467_);
    crate::leanh::lean_ctor_set(v___x_468_, 3, v___x_467_);
    crate::leanh::lean_ctor_set(v___x_468_, 4, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 5, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 6, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 7, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 8, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 9, v___x_466_);
    return v___x_468_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
    v___x_471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_471_, 0, v___x_470_);
    return v___x_471_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_472_: usize = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = 5usize;
    v___x_473_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_474_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
    v___x_476_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__3);
    v___x_477_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_477_, 0, v___x_476_);
    crate::leanh::lean_ctor_set(v___x_477_, 1, v___x_475_);
    crate::leanh::lean_ctor_set(v___x_477_, 2, v___x_473_);
    crate::leanh::lean_ctor_set(v___x_477_, 3, v___x_473_);
    crate::leanh::lean_ctor_set_usize(v___x_477_, 4, v___x_472_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = crate::leanh::lean_box(1);
    v___x_479_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__4);
    v___x_480_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__1);
    v___x_481_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_481_, 0, v___x_480_);
    crate::leanh::lean_ctor_set(v___x_481_, 1, v___x_479_);
    crate::leanh::lean_ctor_set(v___x_481_, 2, v___x_478_);
    return v___x_481_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(
    mut v_msgData_482_: *mut crate::leanh::LeanObject,
    mut v___y_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = lean_st_ref_get(v___y_484_);
    v_env_487_ = crate::leanh::lean_ctor_get(v___x_486_, 0);
    crate::leanh::lean_inc_ref(v_env_487_);
    crate::leanh::lean_dec(v___x_486_);
    v_options_488_ = crate::leanh::lean_ctor_get(v___y_483_, 2);
    v___x_489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__2);
    v___x_490_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___closed__5);
    crate::leanh::lean_inc_ref(v_options_488_);
    v___x_491_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_491_, 0, v_env_487_);
    crate::leanh::lean_ctor_set(v___x_491_, 1, v___x_489_);
    crate::leanh::lean_ctor_set(v___x_491_, 2, v___x_490_);
    crate::leanh::lean_ctor_set(v___x_491_, 3, v_options_488_);
    v___x_492_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_492_, 0, v___x_491_);
    crate::leanh::lean_ctor_set(v___x_492_, 1, v_msgData_482_);
    v___x_493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_493_, 0, v___x_492_);
    return v___x_493_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_msgData_494_: *mut crate::leanh::LeanObject,
    mut v___y_495_: *mut crate::leanh::LeanObject,
    mut v___y_496_: *mut crate::leanh::LeanObject,
    mut v___y_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_498_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v_msgData_494_, v___y_495_, v___y_496_);
    crate::leanh::lean_dec(v___y_496_);
    crate::leanh::lean_dec_ref(v___y_495_);
    return v_res_498_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(
    mut v___y_507_: u8,
    mut v_suppressElabErrors_508_: u8,
    mut v_x_509_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_509_) == 1 {
        let mut v_pre_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_510_ = crate::leanh::lean_ctor_get(v_x_509_, 0);
        match crate::leanh::lean_obj_tag(v_pre_510_) {
            1 => {
                let mut v_pre_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_511_ = crate::leanh::lean_ctor_get(v_pre_510_, 0);
                match crate::leanh::lean_obj_tag(v_pre_511_) {
                    0 => {
                        let mut v_str_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_515_: u8 = 0;
                        v_str_512_ = crate::leanh::lean_ctor_get(v_x_509_, 1);
                        v_str_513_ = crate::leanh::lean_ctor_get(v_pre_510_, 1);
                        v___x_514_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__0;
                        v___x_515_ = lean_string_dec_eq(v_str_513_, v___x_514_);
                        if v___x_515_ == 0 {
                            let mut v___x_516_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_517_: u8 = 0;
                            v___x_516_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__1;
                            v___x_517_ = lean_string_dec_eq(v_str_513_, v___x_516_);
                            if v___x_517_ == 0 {
                                return v___y_507_;
                            } else {
                                let mut v___x_518_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_519_: u8 = 0;
                                v___x_518_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__2;
                                v___x_519_ = lean_string_dec_eq(v_str_512_, v___x_518_);
                                if v___x_519_ == 0 {
                                    return v___y_507_;
                                } else {
                                    return v_suppressElabErrors_508_;
                                }
                            }
                        } else {
                            let mut v___x_520_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_521_: u8 = 0;
                            v___x_520_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__3;
                            v___x_521_ = lean_string_dec_eq(v_str_512_, v___x_520_);
                            if v___x_521_ == 0 {
                                return v___y_507_;
                            } else {
                                return v_suppressElabErrors_508_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_522_ = crate::leanh::lean_ctor_get(v_pre_511_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_522_) == 0 {
                            let mut v_str_523_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_524_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_525_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_526_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_527_: u8 = 0;
                            v_str_523_ = crate::leanh::lean_ctor_get(v_x_509_, 1);
                            v_str_524_ = crate::leanh::lean_ctor_get(v_pre_510_, 1);
                            v_str_525_ = crate::leanh::lean_ctor_get(v_pre_511_, 1);
                            v___x_526_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__4;
                            v___x_527_ = lean_string_dec_eq(v_str_525_, v___x_526_);
                            if v___x_527_ == 0 {
                                return v___y_507_;
                            } else {
                                let mut v___x_528_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_529_: u8 = 0;
                                v___x_528_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__5;
                                v___x_529_ = lean_string_dec_eq(v_str_524_, v___x_528_);
                                if v___x_529_ == 0 {
                                    return v___y_507_;
                                } else {
                                    let mut v___x_530_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_531_: u8 = 0;
                                    v___x_530_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__6;
                                    v___x_531_ = lean_string_dec_eq(v_str_523_, v___x_530_);
                                    if v___x_531_ == 0 {
                                        return v___y_507_;
                                    } else {
                                        return v_suppressElabErrors_508_;
                                    }
                                }
                            }
                        } else {
                            return v___y_507_;
                        }
                    }
                    _ => {
                        return v___y_507_;
                    }
                }
            }
            0 => {
                let mut v_str_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_534_: u8 = 0;
                v_str_532_ = crate::leanh::lean_ctor_get(v_x_509_, 1);
                v___x_533_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___closed__7;
                v___x_534_ = lean_string_dec_eq(v_str_532_, v___x_533_);
                if v___x_534_ == 0 {
                    return v___y_507_;
                } else {
                    return v_suppressElabErrors_508_;
                }
            }
            _ => {
                return v___y_507_;
            }
        }
    } else {
        return v___y_507_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed(
    mut v___y_535_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_536_: *mut crate::leanh::LeanObject,
    mut v_x_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3446__boxed_538_: u8 = 0;
    let mut v_suppressElabErrors_boxed_539_: u8 = 0;
    let mut v_res_540_: u8 = 0;
    let mut v_r_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3446__boxed_538_ = (crate::leanh::lean_unbox(v___y_535_) as u8);
    v_suppressElabErrors_boxed_539_ = (crate::leanh::lean_unbox(v_suppressElabErrors_536_) as u8);
    v_res_540_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0(v___y_3446__boxed_538_, v_suppressElabErrors_boxed_539_, v_x_537_);
    crate::leanh::lean_dec(v_x_537_);
    v_r_541_ = crate::leanh::lean_box((v_res_540_) as usize);
    return v_r_541_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(
    mut v_ref_543_: *mut crate::leanh::LeanObject,
    mut v_msgData_544_: *mut crate::leanh::LeanObject,
    mut v_severity_545_: u8,
    mut v_isSilent_546_: u8,
    mut v___y_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_552_: u8 = 0;
    let mut v___y_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_554_: u8 = 0;
    let mut v___y_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_585_: u8 = 0;
    let mut v___y_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_589_: u8 = 0;
    let mut v___y_590_: u8 = 0;
    let mut v___y_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_593_: u8 = 0;
    let mut v___y_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_600_: u8 = 0;
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_610_: u8 = 0;
    let mut v___y_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_615_: u8 = 0;
    let mut v___y_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_617_: u8 = 0;
    let mut v___y_618_: u8 = 0;
    let mut v___y_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_626_: u8 = 0;
    let mut v___y_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_628_: u8 = 0;
    let mut v___y_629_: u8 = 0;
    let mut v_ref_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___y_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_640_: u8 = 0;
    let mut v___y_641_: u8 = 0;
    let mut v___y_642_: u8 = 0;
    let mut v___y_644_: u8 = 0;
    let mut v_fileName_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_649_: u8 = 0;
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_654_: u8 = 0;
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_634_ = 2;
                v___x_659_ = l_Lean_instBEqMessageSeverity_beq(v_severity_545_, v___x_634_);
                if v___x_659_ == 0 {
                    v___y_644_ = v___x_659_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_544_);
                    v___x_660_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_544_);
                    v___y_644_ = v___x_660_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_560_ = lean_st_ref_take(v___y_559_);
                v_currNamespace_561_ = crate::leanh::lean_ctor_get(v___y_558_, 6);
                v_openDecls_562_ = crate::leanh::lean_ctor_get(v___y_558_, 7);
                v_env_563_ = crate::leanh::lean_ctor_get(v___x_560_, 0);
                v_nextMacroScope_564_ = crate::leanh::lean_ctor_get(v___x_560_, 1);
                v_ngen_565_ = crate::leanh::lean_ctor_get(v___x_560_, 2);
                v_auxDeclNGen_566_ = crate::leanh::lean_ctor_get(v___x_560_, 3);
                v_traceState_567_ = crate::leanh::lean_ctor_get(v___x_560_, 4);
                v_cache_568_ = crate::leanh::lean_ctor_get(v___x_560_, 5);
                v_messages_569_ = crate::leanh::lean_ctor_get(v___x_560_, 6);
                v_infoState_570_ = crate::leanh::lean_ctor_get(v___x_560_, 7);
                v_snapshotTasks_571_ = crate::leanh::lean_ctor_get(v___x_560_, 8);
                v_isSharedCheck_585_ = (!crate::leanh::lean_is_exclusive(v___x_560_)) as u8;
                if v_isSharedCheck_585_ == 0 {
                    v___x_573_ = v___x_560_;
                    v_isShared_574_ = v_isSharedCheck_585_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_571_);
                    crate::leanh::lean_inc(v_infoState_570_);
                    crate::leanh::lean_inc(v_messages_569_);
                    crate::leanh::lean_inc(v_cache_568_);
                    crate::leanh::lean_inc(v_traceState_567_);
                    crate::leanh::lean_inc(v_auxDeclNGen_566_);
                    crate::leanh::lean_inc(v_ngen_565_);
                    crate::leanh::lean_inc(v_nextMacroScope_564_);
                    crate::leanh::lean_inc(v_env_563_);
                    crate::leanh::lean_dec(v___x_560_);
                    v___x_573_ = crate::leanh::lean_box(0);
                    v_isShared_574_ = v_isSharedCheck_585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_562_);
                crate::leanh::lean_inc(v_currNamespace_561_);
                v___x_575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_575_, 0, v_currNamespace_561_);
                crate::leanh::lean_ctor_set(v___x_575_, 1, v_openDecls_562_);
                v___x_576_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_575_);
                crate::leanh::lean_ctor_set(v___x_576_, 1, v___y_557_);
                crate::leanh::lean_inc_ref(v___y_556_);
                crate::leanh::lean_inc_ref(v___y_551_);
                v___x_577_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_577_, 0, v___y_551_);
                crate::leanh::lean_ctor_set(v___x_577_, 1, v___y_555_);
                crate::leanh::lean_ctor_set(v___x_577_, 2, v___y_553_);
                crate::leanh::lean_ctor_set(v___x_577_, 3, v___y_556_);
                crate::leanh::lean_ctor_set(v___x_577_, 4, v___x_576_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_577_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_554_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_577_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_552_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_577_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_546_,
                );
                v___x_578_ = l_Lean_MessageLog_add(v___x_577_, v_messages_569_);
                if v_isShared_574_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_573_, 6, v___x_578_);
                    v___x_580_ = v___x_573_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_584_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 0, v_env_563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 1, v_nextMacroScope_564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 2, v_ngen_565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 3, v_auxDeclNGen_566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 4, v_traceState_567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 5, v_cache_568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 6, v___x_578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 7, v_infoState_570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 8, v_snapshotTasks_571_);
                    v___x_580_ = v_reuseFailAlloc_584_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_581_ = lean_st_ref_set(v___y_559_, v___x_580_);
                v___x_582_ = crate::leanh::lean_box(0);
                v___x_583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_582_);
                return v___x_583_;
            }
            4 => {
                v___x_595_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_544_,
                    );
                v___x_596_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__3(v___x_595_, v___y_547_, v___y_548_);
                v_a_597_ = crate::leanh::lean_ctor_get(v___x_596_, 0);
                v_isSharedCheck_610_ = (!crate::leanh::lean_is_exclusive(v___x_596_)) as u8;
                if v_isSharedCheck_610_ == 0 {
                    v___x_599_ = v___x_596_;
                    v_isShared_600_ = v_isSharedCheck_610_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_597_);
                    crate::leanh::lean_dec(v___x_596_);
                    v___x_599_ = crate::leanh::lean_box(0);
                    v_isShared_600_ = v_isSharedCheck_610_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_592_, 2);
                v___x_601_ = l_Lean_FileMap_toPosition(v___y_592_, v___y_591_);
                crate::leanh::lean_dec(v___y_591_);
                v___x_602_ = l_Lean_FileMap_toPosition(v___y_592_, v___y_594_);
                crate::leanh::lean_dec(v___y_594_);
                v___x_603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_603_, 0, v___x_602_);
                v___x_604_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___closed__0;
                if v___y_590_ == 0 {
                    crate::leanh::lean_del_object(v___x_599_);
                    crate::leanh::lean_dec_ref(v___y_587_);
                    v___y_551_ = v___y_588_;
                    v___y_552_ = v___y_589_;
                    v___y_553_ = v___x_603_;
                    v___y_554_ = v___y_593_;
                    v___y_555_ = v___x_601_;
                    v___y_556_ = v___x_604_;
                    v___y_557_ = v_a_597_;
                    v___y_558_ = v___y_547_;
                    v___y_559_ = v___y_548_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_597_);
                    v___x_605_ = l_Lean_MessageData_hasTag(v___y_587_, v_a_597_);
                    if v___x_605_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_603_, 1);
                        crate::leanh::lean_dec_ref(v___x_601_);
                        crate::leanh::lean_dec(v_a_597_);
                        v___x_606_ = crate::leanh::lean_box(0);
                        if v_isShared_600_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_599_, 0, v___x_606_);
                            v___x_608_ = v___x_599_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
                            v___x_608_ = v_reuseFailAlloc_609_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_599_);
                        v___y_551_ = v___y_588_;
                        v___y_552_ = v___y_589_;
                        v___y_553_ = v___x_603_;
                        v___y_554_ = v___y_593_;
                        v___y_555_ = v___x_601_;
                        v___y_556_ = v___x_604_;
                        v___y_557_ = v_a_597_;
                        v___y_558_ = v___y_547_;
                        v___y_559_ = v___y_548_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_608_;
            }
            7 => {
                v___x_620_ = l_Lean_Syntax_getTailPos_x3f(v___y_614_, v___y_618_);
                crate::leanh::lean_dec(v___y_614_);
                if crate::leanh::lean_obj_tag(v___x_620_) == 0 {
                    crate::leanh::lean_inc(v___y_619_);
                    v___y_587_ = v___y_612_;
                    v___y_588_ = v___y_613_;
                    v___y_589_ = v___y_615_;
                    v___y_590_ = v___y_617_;
                    v___y_591_ = v___y_619_;
                    v___y_592_ = v___y_616_;
                    v___y_593_ = v___y_618_;
                    v___y_594_ = v___y_619_;
                    state = 4;
                    continue;
                } else {
                    v_val_621_ = crate::leanh::lean_ctor_get(v___x_620_, 0);
                    crate::leanh::lean_inc(v_val_621_);
                    crate::leanh::lean_dec_ref_known(v___x_620_, 1);
                    v___y_587_ = v___y_612_;
                    v___y_588_ = v___y_613_;
                    v___y_589_ = v___y_615_;
                    v___y_590_ = v___y_617_;
                    v___y_591_ = v___y_619_;
                    v___y_592_ = v___y_616_;
                    v___y_593_ = v___y_618_;
                    v___y_594_ = v_val_621_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_630_ = l_Lean_replaceRef(v_ref_543_, v___y_625_);
                v___x_631_ = l_Lean_Syntax_getPos_x3f(v_ref_630_, v___y_628_);
                if crate::leanh::lean_obj_tag(v___x_631_) == 0 {
                    v___x_632_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_612_ = v___y_623_;
                    v___y_613_ = v___y_624_;
                    v___y_614_ = v_ref_630_;
                    v___y_615_ = v___y_629_;
                    v___y_616_ = v___y_627_;
                    v___y_617_ = v___y_626_;
                    v___y_618_ = v___y_628_;
                    v___y_619_ = v___x_632_;
                    state = 7;
                    continue;
                } else {
                    v_val_633_ = crate::leanh::lean_ctor_get(v___x_631_, 0);
                    crate::leanh::lean_inc(v_val_633_);
                    crate::leanh::lean_dec_ref_known(v___x_631_, 1);
                    v___y_612_ = v___y_623_;
                    v___y_613_ = v___y_624_;
                    v___y_614_ = v_ref_630_;
                    v___y_615_ = v___y_629_;
                    v___y_616_ = v___y_627_;
                    v___y_617_ = v___y_626_;
                    v___y_618_ = v___y_628_;
                    v___y_619_ = v_val_633_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_642_ == 0 {
                    v___y_623_ = v___y_638_;
                    v___y_624_ = v___y_637_;
                    v___y_625_ = v___y_636_;
                    v___y_626_ = v___y_640_;
                    v___y_627_ = v___y_639_;
                    v___y_628_ = v___y_641_;
                    v___y_629_ = v_severity_545_;
                    state = 8;
                    continue;
                } else {
                    v___y_623_ = v___y_638_;
                    v___y_624_ = v___y_637_;
                    v___y_625_ = v___y_636_;
                    v___y_626_ = v___y_640_;
                    v___y_627_ = v___y_639_;
                    v___y_628_ = v___y_641_;
                    v___y_629_ = v___x_634_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_644_ == 0 {
                    v_fileName_645_ = crate::leanh::lean_ctor_get(v___y_547_, 0);
                    v_fileMap_646_ = crate::leanh::lean_ctor_get(v___y_547_, 1);
                    v_options_647_ = crate::leanh::lean_ctor_get(v___y_547_, 2);
                    v_ref_648_ = crate::leanh::lean_ctor_get(v___y_547_, 5);
                    v_suppressElabErrors_649_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_547_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_650_ = crate::leanh::lean_box((v___y_644_) as usize);
                    v___x_651_ = crate::leanh::lean_box((v_suppressElabErrors_649_) as usize);
                    v___f_652_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_652_, 0, v___x_650_);
                    crate::leanh::lean_closure_set(v___f_652_, 1, v___x_651_);
                    v___x_653_ = 1;
                    v___x_654_ = l_Lean_instBEqMessageSeverity_beq(v_severity_545_, v___x_653_);
                    if v___x_654_ == 0 {
                        v___y_636_ = v_ref_648_;
                        v___y_637_ = v_fileName_645_;
                        v___y_638_ = v___f_652_;
                        v___y_639_ = v_fileMap_646_;
                        v___y_640_ = v_suppressElabErrors_649_;
                        v___y_641_ = v___y_644_;
                        v___y_642_ = v___x_654_;
                        state = 9;
                        continue;
                    } else {
                        v___x_655_ = l_Lean_warningAsError;
                        v___x_656_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2_spec__4(v_options_647_, v___x_655_);
                        v___y_636_ = v_ref_648_;
                        v___y_637_ = v_fileName_645_;
                        v___y_638_ = v___f_652_;
                        v___y_639_ = v_fileMap_646_;
                        v___y_640_ = v_suppressElabErrors_649_;
                        v___y_641_ = v___y_644_;
                        v___y_642_ = v___x_656_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_544_);
                    v___x_657_ = crate::leanh::lean_box(0);
                    v___x_658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_658_, 0, v___x_657_);
                    return v___x_658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2___boxed(
    mut v_ref_661_: *mut crate::leanh::LeanObject,
    mut v_msgData_662_: *mut crate::leanh::LeanObject,
    mut v_severity_663_: *mut crate::leanh::LeanObject,
    mut v_isSilent_664_: *mut crate::leanh::LeanObject,
    mut v___y_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
    mut v___y_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_668_: u8 = 0;
    let mut v_isSilent_boxed_669_: u8 = 0;
    let mut v_res_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_668_ = (crate::leanh::lean_unbox(v_severity_663_) as u8);
    v_isSilent_boxed_669_ = (crate::leanh::lean_unbox(v_isSilent_664_) as u8);
    v_res_670_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_661_, v_msgData_662_, v_severity_boxed_668_, v_isSilent_boxed_669_, v___y_665_, v___y_666_);
    crate::leanh::lean_dec(v___y_666_);
    crate::leanh::lean_dec_ref(v___y_665_);
    crate::leanh::lean_dec(v_ref_661_);
    return v_res_670_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(
    mut v_msgData_671_: *mut crate::leanh::LeanObject,
    mut v_severity_672_: u8,
    mut v_isSilent_673_: u8,
    mut v___y_674_: *mut crate::leanh::LeanObject,
    mut v___y_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_677_ = crate::leanh::lean_ctor_get(v___y_674_, 5);
    v___x_678_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1_spec__2(v_ref_677_, v_msgData_671_, v_severity_672_, v_isSilent_673_, v___y_674_, v___y_675_);
    return v___x_678_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1___boxed(
    mut v_msgData_679_: *mut crate::leanh::LeanObject,
    mut v_severity_680_: *mut crate::leanh::LeanObject,
    mut v_isSilent_681_: *mut crate::leanh::LeanObject,
    mut v___y_682_: *mut crate::leanh::LeanObject,
    mut v___y_683_: *mut crate::leanh::LeanObject,
    mut v___y_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_685_: u8 = 0;
    let mut v_isSilent_boxed_686_: u8 = 0;
    let mut v_res_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_685_ = (crate::leanh::lean_unbox(v_severity_680_) as u8);
    v_isSilent_boxed_686_ = (crate::leanh::lean_unbox(v_isSilent_681_) as u8);
    v_res_687_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(
        v_msgData_679_,
        v_severity_boxed_685_,
        v_isSilent_boxed_686_,
        v___y_682_,
        v___y_683_,
    );
    crate::leanh::lean_dec(v___y_683_);
    crate::leanh::lean_dec_ref(v___y_682_);
    return v_res_687_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkExponent_spec__1(
    mut v_msgData_688_: *mut crate::leanh::LeanObject,
    mut v___y_689_: *mut crate::leanh::LeanObject,
    mut v___y_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = 1;
    v___x_693_ = 0;
    v___x_694_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkExponent_spec__1_spec__1(
        v_msgData_688_,
        v___x_692_,
        v___x_693_,
        v___y_689_,
        v___y_690_,
    );
    return v___x_694_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkExponent_spec__1___boxed(
    mut v_msgData_695_: *mut crate::leanh::LeanObject,
    mut v___y_696_: *mut crate::leanh::LeanObject,
    mut v___y_697_: *mut crate::leanh::LeanObject,
    mut v___y_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_699_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(
        v_msgData_695_,
        v___y_696_,
        v___y_697_,
    );
    crate::leanh::lean_dec(v___y_697_);
    crate::leanh::lean_dec_ref(v___y_696_);
    return v_res_699_;
}
pub unsafe fn l_Lean_checkExponent(
    mut v_n_708_: *mut crate::leanh::LeanObject,
    mut v_warning_709_: u8,
    mut v_a_710_: *mut crate::leanh::LeanObject,
    mut v_a_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v___x_730_: u8 = 0;
    let mut v_name_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: u8 = 0;
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_reuseFailAlloc_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_717_ = crate::leanh::lean_ctor_get(v_a_710_, 2);
                v___x_718_ = l_Lean_exponentiation_threshold;
                v___x_719_ = l_Lean_Option_get___at___00Lean_checkExponent_spec__0(
                    v_options_717_,
                    v___x_718_,
                );
                v___x_720_ = lean_nat_dec_lt(v___x_719_, v_n_708_);
                if v___x_720_ == 0 {
                    crate::leanh::lean_dec(v___x_719_);
                    crate::leanh::lean_dec(v_n_708_);
                    v___x_721_ = 1;
                    v___x_722_ = crate::leanh::lean_box((v___x_721_) as usize);
                    v___x_723_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_722_);
                    return v___x_723_;
                } else {
                    if v_warning_709_ == 0 {
                        crate::leanh::lean_dec(v___x_719_);
                        crate::leanh::lean_dec(v_n_708_);
                        state = 1;
                        continue;
                    } else {
                        v___x_724_ = l_Lean_checkExponent___closed__1;
                        v___x_725_ = l_Lean_logMessageKind___redArg(v___x_724_, v_a_711_);
                        if crate::leanh::lean_obj_tag(v___x_725_) == 0 {
                            v_a_726_ = crate::leanh::lean_ctor_get(v___x_725_, 0);
                            v_isSharedCheck_759_ =
                                (!crate::leanh::lean_is_exclusive(v___x_725_)) as u8;
                            if v_isSharedCheck_759_ == 0 {
                                v___x_728_ = v___x_725_;
                                v_isShared_729_ = v_isSharedCheck_759_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_726_);
                                crate::leanh::lean_dec(v___x_725_);
                                v___x_728_ = crate::leanh::lean_box(0);
                                v_isShared_729_ = v_isSharedCheck_759_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_719_);
                            crate::leanh::lean_dec(v_n_708_);
                            return v___x_725_;
                        }
                    }
                }
            }
            1 => {
                v___x_714_ = 0;
                v___x_715_ = crate::leanh::lean_box((v___x_714_) as usize);
                v___x_716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_716_, 0, v___x_715_);
                return v___x_716_;
            }
            2 => {
                v___x_730_ = (crate::leanh::lean_unbox(v_a_726_) as u8);
                if v___x_730_ == 0 {
                    crate::leanh::lean_del_object(v___x_728_);
                    crate::leanh::lean_dec(v_a_726_);
                    crate::leanh::lean_dec(v___x_719_);
                    crate::leanh::lean_dec(v_n_708_);
                    state = 1;
                    continue;
                } else {
                    v_name_731_ = crate::leanh::lean_ctor_get(v___x_718_, 0);
                    v___x_732_ = l_Lean_checkExponent___closed__2;
                    v___x_733_ = l_Nat_reprFast(v_n_708_);
                    v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
                    crate::leanh::lean_dec_ref(v___x_733_);
                    v___x_735_ = l_Lean_checkExponent___closed__3;
                    v___x_736_ = lean_string_append(v___x_734_, v___x_735_);
                    v___x_737_ = l_Nat_reprFast(v___x_719_);
                    v___x_738_ = lean_string_append(v___x_736_, v___x_737_);
                    crate::leanh::lean_dec_ref(v___x_737_);
                    v___x_739_ = l_Lean_checkExponent___closed__4;
                    v___x_740_ = lean_string_append(v___x_738_, v___x_739_);
                    v___x_741_ = (crate::leanh::lean_unbox(v_a_726_) as u8);
                    crate::leanh::lean_dec(v_a_726_);
                    crate::leanh::lean_inc(v_name_731_);
                    v___x_742_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_731_,
                        v___x_741_,
                    );
                    v___x_743_ = lean_string_append(v___x_740_, v___x_742_);
                    crate::leanh::lean_dec_ref(v___x_742_);
                    v___x_744_ = l_Lean_checkExponent___closed__5;
                    v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
                    if v_isShared_729_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_728_, 3);
                        crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_745_);
                        v___x_747_ = v___x_728_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_758_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_745_);
                        v___x_747_ = v_reuseFailAlloc_758_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_748_ = l_Lean_MessageData_ofFormat(v___x_747_);
                v___x_749_ = l_Lean_logWarning___at___00Lean_checkExponent_spec__1(
                    v___x_748_, v_a_710_, v_a_711_,
                );
                if crate::leanh::lean_obj_tag(v___x_749_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_749_, 1);
                    state = 1;
                    continue;
                } else {
                    v_a_750_ = crate::leanh::lean_ctor_get(v___x_749_, 0);
                    v_isSharedCheck_757_ = (!crate::leanh::lean_is_exclusive(v___x_749_)) as u8;
                    if v_isSharedCheck_757_ == 0 {
                        v___x_752_ = v___x_749_;
                        v_isShared_753_ = v_isSharedCheck_757_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_750_);
                        crate::leanh::lean_dec(v___x_749_);
                        v___x_752_ = crate::leanh::lean_box(0);
                        v_isShared_753_ = v_isSharedCheck_757_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_753_ == 0 {
                    v___x_755_ = v___x_752_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
                    v___x_755_ = v_reuseFailAlloc_756_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_checkExponent___boxed(
    mut v_n_760_: *mut crate::leanh::LeanObject,
    mut v_warning_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_warning_boxed_765_: u8 = 0;
    let mut v_res_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_warning_boxed_765_ = (crate::leanh::lean_unbox(v_warning_761_) as u8);
    v_res_766_ = l_Lean_checkExponent(v_n_760_, v_warning_boxed_765_, v_a_762_, v_a_763_);
    crate::leanh::lean_dec(v_a_763_);
    crate::leanh::lean_dec_ref(v_a_762_);
    return v_res_766_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_SafeExponentiation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_SafeExponentiation_0__Lean_initFn_00___x40_Lean_Util_SafeExponentiation_3025597618____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_exponentiation_threshold = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_exponentiation_threshold);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_SafeExponentiation(
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
pub unsafe fn initialize_Lean_Util_SafeExponentiation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_SafeExponentiation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_SafeExponentiation(builtin);
}
