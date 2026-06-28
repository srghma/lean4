// Lean compiler output
// Module: Lake.DSL.Attributes
// Imports: Lake.DSL.AttributesCore
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lake::DSL::AttributesCore::{
    initialize_Lake_DSL_AttributesCore, l_Lake_testDriverAttr,
    runtime_initialize_Lake_DSL_AttributesCore,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [64, 91, 116, 101, 115, 116, 95, 114, 117, 110, 110, 101, 114, 93, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 44, 32, 117, 115, 101, 32, 64, 91, 116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 93, 32, 105, 110, 115, 116, 101, 97, 100, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12997130533650095963 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 83, 76, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11286550318989764116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17519352592304664597 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6795554283374303104 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8998729796134954088 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8787786452389294981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,361638869280322168 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7717359171895508208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16553551316016363163 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8707057893190586918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 101, 115, 116, 95, 114, 117, 110, 110, 101, 114, 0]};
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1189756298301750343 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_347_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0);
    v___x_349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_349_, 0, v___x_348_);
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1);
    v___x_351_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_352_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_352_, 0, v___x_351_);
    crate::leanh::lean_ctor_set(v___x_352_, 1, v___x_351_);
    crate::leanh::lean_ctor_set(v___x_352_, 2, v___x_351_);
    crate::leanh::lean_ctor_set(v___x_352_, 3, v___x_351_);
    crate::leanh::lean_ctor_set(v___x_352_, 4, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_352_, 5, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_352_, 6, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_352_, 7, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_352_, 8, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_352_, 9, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
    v___x_355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_355_, 0, v___x_354_);
    return v___x_355_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_356_: usize = 0;
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = 5usize;
    v___x_357_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_358_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
    v___x_360_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3);
    v___x_361_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_361_, 0, v___x_360_);
    crate::leanh::lean_ctor_set(v___x_361_, 1, v___x_359_);
    crate::leanh::lean_ctor_set(v___x_361_, 2, v___x_357_);
    crate::leanh::lean_ctor_set(v___x_361_, 3, v___x_357_);
    crate::leanh::lean_ctor_set_usize(v___x_361_, 4, v___x_356_);
    return v___x_361_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = crate::leanh::lean_box(1);
    v___x_363_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4);
    v___x_364_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1);
    v___x_365_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_365_, 0, v___x_364_);
    crate::leanh::lean_ctor_set(v___x_365_, 1, v___x_363_);
    crate::leanh::lean_ctor_set(v___x_365_, 2, v___x_362_);
    return v___x_365_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_msgData_366_: *mut crate::leanh::LeanObject,
    mut v___y_367_: *mut crate::leanh::LeanObject,
    mut v___y_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = lean_st_ref_get(v___y_368_);
    v_env_371_ = crate::leanh::lean_ctor_get(v___x_370_, 0);
    crate::leanh::lean_inc_ref(v_env_371_);
    crate::leanh::lean_dec(v___x_370_);
    v_options_372_ = crate::leanh::lean_ctor_get(v___y_367_, 2);
    v___x_373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2);
    v___x_374_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5);
    crate::leanh::lean_inc_ref(v_options_372_);
    v___x_375_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_375_, 0, v_env_371_);
    crate::leanh::lean_ctor_set(v___x_375_, 1, v___x_373_);
    crate::leanh::lean_ctor_set(v___x_375_, 2, v___x_374_);
    crate::leanh::lean_ctor_set(v___x_375_, 3, v_options_372_);
    v___x_376_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_376_, 0, v___x_375_);
    crate::leanh::lean_ctor_set(v___x_376_, 1, v_msgData_366_);
    v___x_377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_376_);
    return v___x_377_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_msgData_378_: *mut crate::leanh::LeanObject,
    mut v___y_379_: *mut crate::leanh::LeanObject,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_msgData_378_, v___y_379_, v___y_380_);
    crate::leanh::lean_dec(v___y_380_);
    crate::leanh::lean_dec_ref(v___y_379_);
    return v_res_382_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0(
    mut v___y_391_: u8,
    mut v_suppressElabErrors_392_: u8,
    mut v_x_393_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_393_) == 1 {
        let mut v_pre_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_394_ = crate::leanh::lean_ctor_get(v_x_393_, 0);
        match crate::leanh::lean_obj_tag(v_pre_394_) {
            1 => {
                let mut v_pre_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_395_ = crate::leanh::lean_ctor_get(v_pre_394_, 0);
                match crate::leanh::lean_obj_tag(v_pre_395_) {
                    0 => {
                        let mut v_str_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_399_: u8 = 0;
                        v_str_396_ = crate::leanh::lean_ctor_get(v_x_393_, 1);
                        v_str_397_ = crate::leanh::lean_ctor_get(v_pre_394_, 1);
                        v___x_398_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0;
                        v___x_399_ = lean_string_dec_eq(v_str_397_, v___x_398_);
                        if v___x_399_ == 0 {
                            let mut v___x_400_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_401_: u8 = 0;
                            v___x_400_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1;
                            v___x_401_ = lean_string_dec_eq(v_str_397_, v___x_400_);
                            if v___x_401_ == 0 {
                                return v___y_391_;
                            } else {
                                let mut v___x_402_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_403_: u8 = 0;
                                v___x_402_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2;
                                v___x_403_ = lean_string_dec_eq(v_str_396_, v___x_402_);
                                if v___x_403_ == 0 {
                                    return v___y_391_;
                                } else {
                                    return v_suppressElabErrors_392_;
                                }
                            }
                        } else {
                            let mut v___x_404_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_405_: u8 = 0;
                            v___x_404_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3;
                            v___x_405_ = lean_string_dec_eq(v_str_396_, v___x_404_);
                            if v___x_405_ == 0 {
                                return v___y_391_;
                            } else {
                                return v_suppressElabErrors_392_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_406_ = crate::leanh::lean_ctor_get(v_pre_395_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_406_) == 0 {
                            let mut v_str_407_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_408_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_409_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_410_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_411_: u8 = 0;
                            v_str_407_ = crate::leanh::lean_ctor_get(v_x_393_, 1);
                            v_str_408_ = crate::leanh::lean_ctor_get(v_pre_394_, 1);
                            v_str_409_ = crate::leanh::lean_ctor_get(v_pre_395_, 1);
                            v___x_410_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4;
                            v___x_411_ = lean_string_dec_eq(v_str_409_, v___x_410_);
                            if v___x_411_ == 0 {
                                return v___y_391_;
                            } else {
                                let mut v___x_412_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_413_: u8 = 0;
                                v___x_412_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5;
                                v___x_413_ = lean_string_dec_eq(v_str_408_, v___x_412_);
                                if v___x_413_ == 0 {
                                    return v___y_391_;
                                } else {
                                    let mut v___x_414_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_415_: u8 = 0;
                                    v___x_414_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6;
                                    v___x_415_ = lean_string_dec_eq(v_str_407_, v___x_414_);
                                    if v___x_415_ == 0 {
                                        return v___y_391_;
                                    } else {
                                        return v_suppressElabErrors_392_;
                                    }
                                }
                            }
                        } else {
                            return v___y_391_;
                        }
                    }
                    _ => {
                        return v___y_391_;
                    }
                }
            }
            0 => {
                let mut v_str_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_418_: u8 = 0;
                v_str_416_ = crate::leanh::lean_ctor_get(v_x_393_, 1);
                v___x_417_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7;
                v___x_418_ = lean_string_dec_eq(v_str_416_, v___x_417_);
                if v___x_418_ == 0 {
                    return v___y_391_;
                } else {
                    return v_suppressElabErrors_392_;
                }
            }
            _ => {
                return v___y_391_;
            }
        }
    } else {
        return v___y_391_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(
    mut v___y_419_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_420_: *mut crate::leanh::LeanObject,
    mut v_x_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2500__boxed_422_: u8 = 0;
    let mut v_suppressElabErrors_boxed_423_: u8 = 0;
    let mut v_res_424_: u8 = 0;
    let mut v_r_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_2500__boxed_422_ = (crate::leanh::lean_unbox(v___y_419_) as u8);
    v_suppressElabErrors_boxed_423_ = (crate::leanh::lean_unbox(v_suppressElabErrors_420_) as u8);
    v_res_424_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0(v___y_2500__boxed_422_, v_suppressElabErrors_boxed_423_, v_x_421_);
    crate::leanh::lean_dec(v_x_421_);
    v_r_425_ = crate::leanh::lean_box((v_res_424_) as usize);
    return v_r_425_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_opts_426_: *mut crate::leanh::LeanObject,
    mut v_opt_427_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_428_ = crate::leanh::lean_ctor_get(v_opt_427_, 0);
    v_defValue_429_ = crate::leanh::lean_ctor_get(v_opt_427_, 1);
    v_map_430_ = crate::leanh::lean_ctor_get(v_opts_426_, 0);
    v___x_431_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_430_,
            v_name_428_,
        );
    if crate::leanh::lean_obj_tag(v___x_431_) == 0 {
        let mut v___x_432_: u8 = 0;
        v___x_432_ = (crate::leanh::lean_unbox(v_defValue_429_) as u8);
        return v___x_432_;
    } else {
        let mut v_val_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_433_ = crate::leanh::lean_ctor_get(v___x_431_, 0);
        crate::leanh::lean_inc(v_val_433_);
        crate::leanh::lean_dec_ref_known(v___x_431_, 1);
        if crate::leanh::lean_obj_tag(v_val_433_) == 1 {
            let mut v_v_434_: u8 = 0;
            v_v_434_ = crate::leanh::lean_ctor_get_uint8(v_val_433_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_433_, 0);
            return v_v_434_;
        } else {
            let mut v___x_435_: u8 = 0;
            crate::leanh::lean_dec(v_val_433_);
            v___x_435_ = (crate::leanh::lean_unbox(v_defValue_429_) as u8);
            return v___x_435_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(
    mut v_opts_436_: *mut crate::leanh::LeanObject,
    mut v_opt_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_438_: u8 = 0;
    let mut v_r_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_opts_436_, v_opt_437_);
    crate::leanh::lean_dec_ref(v_opt_437_);
    crate::leanh::lean_dec_ref(v_opts_436_);
    v_r_439_ = crate::leanh::lean_box((v_res_438_) as usize);
    return v_r_439_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0(
    mut v_ref_441_: *mut crate::leanh::LeanObject,
    mut v_msgData_442_: *mut crate::leanh::LeanObject,
    mut v_severity_443_: u8,
    mut v_isSilent_444_: u8,
    mut v___y_445_: *mut crate::leanh::LeanObject,
    mut v___y_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_453_: u8 = 0;
    let mut v___y_454_: u8 = 0;
    let mut v___y_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_483_: u8 = 0;
    let mut v___y_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_487_: u8 = 0;
    let mut v___y_488_: u8 = 0;
    let mut v___y_489_: u8 = 0;
    let mut v___y_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u8 = 0;
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut v___y_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_512_: u8 = 0;
    let mut v___y_513_: u8 = 0;
    let mut v___y_514_: u8 = 0;
    let mut v___y_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_523_: u8 = 0;
    let mut v___y_524_: u8 = 0;
    let mut v___y_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_527_: u8 = 0;
    let mut v_ref_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    let mut v___y_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_537_: u8 = 0;
    let mut v___y_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_539_: u8 = 0;
    let mut v___y_540_: u8 = 0;
    let mut v___y_542_: u8 = 0;
    let mut v_fileName_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_547_: u8 = 0;
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: u8 = 0;
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: u8 = 0;
    let mut v___x_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_532_ = 2;
                v___x_557_ = l_Lean_instBEqMessageSeverity_beq(v_severity_443_, v___x_532_);
                if v___x_557_ == 0 {
                    v___y_542_ = v___x_557_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_442_);
                    v___x_558_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_442_);
                    v___y_542_ = v___x_558_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_458_ = lean_st_ref_take(v___y_457_);
                v_currNamespace_459_ = crate::leanh::lean_ctor_get(v___y_456_, 6);
                v_openDecls_460_ = crate::leanh::lean_ctor_get(v___y_456_, 7);
                v_env_461_ = crate::leanh::lean_ctor_get(v___x_458_, 0);
                v_nextMacroScope_462_ = crate::leanh::lean_ctor_get(v___x_458_, 1);
                v_ngen_463_ = crate::leanh::lean_ctor_get(v___x_458_, 2);
                v_auxDeclNGen_464_ = crate::leanh::lean_ctor_get(v___x_458_, 3);
                v_traceState_465_ = crate::leanh::lean_ctor_get(v___x_458_, 4);
                v_cache_466_ = crate::leanh::lean_ctor_get(v___x_458_, 5);
                v_messages_467_ = crate::leanh::lean_ctor_get(v___x_458_, 6);
                v_infoState_468_ = crate::leanh::lean_ctor_get(v___x_458_, 7);
                v_snapshotTasks_469_ = crate::leanh::lean_ctor_get(v___x_458_, 8);
                v_isSharedCheck_483_ = (!crate::leanh::lean_is_exclusive(v___x_458_)) as u8;
                if v_isSharedCheck_483_ == 0 {
                    v___x_471_ = v___x_458_;
                    v_isShared_472_ = v_isSharedCheck_483_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_469_);
                    crate::leanh::lean_inc(v_infoState_468_);
                    crate::leanh::lean_inc(v_messages_467_);
                    crate::leanh::lean_inc(v_cache_466_);
                    crate::leanh::lean_inc(v_traceState_465_);
                    crate::leanh::lean_inc(v_auxDeclNGen_464_);
                    crate::leanh::lean_inc(v_ngen_463_);
                    crate::leanh::lean_inc(v_nextMacroScope_462_);
                    crate::leanh::lean_inc(v_env_461_);
                    crate::leanh::lean_dec(v___x_458_);
                    v___x_471_ = crate::leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_460_);
                crate::leanh::lean_inc(v_currNamespace_459_);
                v___x_473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_473_, 0, v_currNamespace_459_);
                crate::leanh::lean_ctor_set(v___x_473_, 1, v_openDecls_460_);
                v___x_474_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_474_, 0, v___x_473_);
                crate::leanh::lean_ctor_set(v___x_474_, 1, v___y_451_);
                crate::leanh::lean_inc_ref(v___y_449_);
                crate::leanh::lean_inc_ref(v___y_452_);
                v___x_475_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_475_, 0, v___y_452_);
                crate::leanh::lean_ctor_set(v___x_475_, 1, v___y_455_);
                crate::leanh::lean_ctor_set(v___x_475_, 2, v___y_450_);
                crate::leanh::lean_ctor_set(v___x_475_, 3, v___y_449_);
                crate::leanh::lean_ctor_set(v___x_475_, 4, v___x_474_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_453_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_454_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_444_,
                );
                v___x_476_ = l_Lean_MessageLog_add(v___x_475_, v_messages_467_);
                if v_isShared_472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_471_, 6, v___x_476_);
                    v___x_478_ = v___x_471_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_482_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 0, v_env_461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 1, v_nextMacroScope_462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 2, v_ngen_463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 3, v_auxDeclNGen_464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 4, v_traceState_465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 5, v_cache_466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 6, v___x_476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 7, v_infoState_468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 8, v_snapshotTasks_469_);
                    v___x_478_ = v_reuseFailAlloc_482_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_479_ = lean_st_ref_set(v___y_457_, v___x_478_);
                v___x_480_ = crate::leanh::lean_box(0);
                v___x_481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_481_, 0, v___x_480_);
                return v___x_481_;
            }
            4 => {
                v___x_493_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_442_,
                    );
                v___x_494_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_493_, v___y_445_, v___y_446_);
                v_a_495_ = crate::leanh::lean_ctor_get(v___x_494_, 0);
                v_isSharedCheck_508_ = (!crate::leanh::lean_is_exclusive(v___x_494_)) as u8;
                if v_isSharedCheck_508_ == 0 {
                    v___x_497_ = v___x_494_;
                    v_isShared_498_ = v_isSharedCheck_508_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_495_);
                    crate::leanh::lean_dec(v___x_494_);
                    v___x_497_ = crate::leanh::lean_box(0);
                    v_isShared_498_ = v_isSharedCheck_508_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_491_, 2);
                v___x_499_ = l_Lean_FileMap_toPosition(v___y_491_, v___y_490_);
                crate::leanh::lean_dec(v___y_490_);
                v___x_500_ = l_Lean_FileMap_toPosition(v___y_491_, v___y_492_);
                crate::leanh::lean_dec(v___y_492_);
                v___x_501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_501_, 0, v___x_500_);
                v___x_502_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___closed__0;
                if v___y_487_ == 0 {
                    crate::leanh::lean_del_object(v___x_497_);
                    crate::leanh::lean_dec_ref(v___y_485_);
                    v___y_449_ = v___x_502_;
                    v___y_450_ = v___x_501_;
                    v___y_451_ = v_a_495_;
                    v___y_452_ = v___y_486_;
                    v___y_453_ = v___y_488_;
                    v___y_454_ = v___y_489_;
                    v___y_455_ = v___x_499_;
                    v___y_456_ = v___y_445_;
                    v___y_457_ = v___y_446_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_495_);
                    v___x_503_ = l_Lean_MessageData_hasTag(v___y_485_, v_a_495_);
                    if v___x_503_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_501_, 1);
                        crate::leanh::lean_dec_ref(v___x_499_);
                        crate::leanh::lean_dec(v_a_495_);
                        v___x_504_ = crate::leanh::lean_box(0);
                        if v_isShared_498_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_497_, 0, v___x_504_);
                            v___x_506_ = v___x_497_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
                            v___x_506_ = v_reuseFailAlloc_507_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_497_);
                        v___y_449_ = v___x_502_;
                        v___y_450_ = v___x_501_;
                        v___y_451_ = v_a_495_;
                        v___y_452_ = v___y_486_;
                        v___y_453_ = v___y_488_;
                        v___y_454_ = v___y_489_;
                        v___y_455_ = v___x_499_;
                        v___y_456_ = v___y_445_;
                        v___y_457_ = v___y_446_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_506_;
            }
            7 => {
                v___x_518_ = l_Lean_Syntax_getTailPos_x3f(v___y_516_, v___y_512_);
                crate::leanh::lean_dec(v___y_516_);
                if crate::leanh::lean_obj_tag(v___x_518_) == 0 {
                    crate::leanh::lean_inc(v___y_517_);
                    v___y_485_ = v___y_510_;
                    v___y_486_ = v___y_511_;
                    v___y_487_ = v___y_513_;
                    v___y_488_ = v___y_512_;
                    v___y_489_ = v___y_514_;
                    v___y_490_ = v___y_517_;
                    v___y_491_ = v___y_515_;
                    v___y_492_ = v___y_517_;
                    state = 4;
                    continue;
                } else {
                    v_val_519_ = crate::leanh::lean_ctor_get(v___x_518_, 0);
                    crate::leanh::lean_inc(v_val_519_);
                    crate::leanh::lean_dec_ref_known(v___x_518_, 1);
                    v___y_485_ = v___y_510_;
                    v___y_486_ = v___y_511_;
                    v___y_487_ = v___y_513_;
                    v___y_488_ = v___y_512_;
                    v___y_489_ = v___y_514_;
                    v___y_490_ = v___y_517_;
                    v___y_491_ = v___y_515_;
                    v___y_492_ = v_val_519_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_528_ = l_Lean_replaceRef(v_ref_441_, v___y_525_);
                v___x_529_ = l_Lean_Syntax_getPos_x3f(v_ref_528_, v___y_524_);
                if crate::leanh::lean_obj_tag(v___x_529_) == 0 {
                    v___x_530_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_510_ = v___y_521_;
                    v___y_511_ = v___y_522_;
                    v___y_512_ = v___y_524_;
                    v___y_513_ = v___y_523_;
                    v___y_514_ = v___y_527_;
                    v___y_515_ = v___y_526_;
                    v___y_516_ = v_ref_528_;
                    v___y_517_ = v___x_530_;
                    state = 7;
                    continue;
                } else {
                    v_val_531_ = crate::leanh::lean_ctor_get(v___x_529_, 0);
                    crate::leanh::lean_inc(v_val_531_);
                    crate::leanh::lean_dec_ref_known(v___x_529_, 1);
                    v___y_510_ = v___y_521_;
                    v___y_511_ = v___y_522_;
                    v___y_512_ = v___y_524_;
                    v___y_513_ = v___y_523_;
                    v___y_514_ = v___y_527_;
                    v___y_515_ = v___y_526_;
                    v___y_516_ = v_ref_528_;
                    v___y_517_ = v_val_531_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_540_ == 0 {
                    v___y_521_ = v___y_535_;
                    v___y_522_ = v___y_534_;
                    v___y_523_ = v___y_537_;
                    v___y_524_ = v___y_539_;
                    v___y_525_ = v___y_536_;
                    v___y_526_ = v___y_538_;
                    v___y_527_ = v_severity_443_;
                    state = 8;
                    continue;
                } else {
                    v___y_521_ = v___y_535_;
                    v___y_522_ = v___y_534_;
                    v___y_523_ = v___y_537_;
                    v___y_524_ = v___y_539_;
                    v___y_525_ = v___y_536_;
                    v___y_526_ = v___y_538_;
                    v___y_527_ = v___x_532_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_542_ == 0 {
                    v_fileName_543_ = crate::leanh::lean_ctor_get(v___y_445_, 0);
                    v_fileMap_544_ = crate::leanh::lean_ctor_get(v___y_445_, 1);
                    v_options_545_ = crate::leanh::lean_ctor_get(v___y_445_, 2);
                    v_ref_546_ = crate::leanh::lean_ctor_get(v___y_445_, 5);
                    v_suppressElabErrors_547_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_445_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_548_ = crate::leanh::lean_box((v___y_542_) as usize);
                    v___x_549_ = crate::leanh::lean_box((v_suppressElabErrors_547_) as usize);
                    v___f_550_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_550_, 0, v___x_548_);
                    crate::leanh::lean_closure_set(v___f_550_, 1, v___x_549_);
                    v___x_551_ = 1;
                    v___x_552_ = l_Lean_instBEqMessageSeverity_beq(v_severity_443_, v___x_551_);
                    if v___x_552_ == 0 {
                        v___y_534_ = v_fileName_543_;
                        v___y_535_ = v___f_550_;
                        v___y_536_ = v_ref_546_;
                        v___y_537_ = v_suppressElabErrors_547_;
                        v___y_538_ = v_fileMap_544_;
                        v___y_539_ = v___y_542_;
                        v___y_540_ = v___x_552_;
                        state = 9;
                        continue;
                    } else {
                        v___x_553_ = l_Lean_warningAsError;
                        v___x_554_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_options_545_, v___x_553_);
                        v___y_534_ = v_fileName_543_;
                        v___y_535_ = v___f_550_;
                        v___y_536_ = v_ref_546_;
                        v___y_537_ = v_suppressElabErrors_547_;
                        v___y_538_ = v_fileMap_544_;
                        v___y_539_ = v___y_542_;
                        v___y_540_ = v___x_554_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_442_);
                    v___x_555_ = crate::leanh::lean_box(0);
                    v___x_556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_556_, 0, v___x_555_);
                    return v___x_556_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_ref_559_: *mut crate::leanh::LeanObject,
    mut v_msgData_560_: *mut crate::leanh::LeanObject,
    mut v_severity_561_: *mut crate::leanh::LeanObject,
    mut v_isSilent_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
    mut v___y_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_566_: u8 = 0;
    let mut v_isSilent_boxed_567_: u8 = 0;
    let mut v_res_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_566_ = (crate::leanh::lean_unbox(v_severity_561_) as u8);
    v_isSilent_boxed_567_ = (crate::leanh::lean_unbox(v_isSilent_562_) as u8);
    v_res_568_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0(v_ref_559_, v_msgData_560_, v_severity_boxed_566_, v_isSilent_boxed_567_, v___y_563_, v___y_564_);
    crate::leanh::lean_dec(v___y_564_);
    crate::leanh::lean_dec_ref(v___y_563_);
    crate::leanh::lean_dec(v_ref_559_);
    return v_res_568_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0(
    mut v_ref_569_: *mut crate::leanh::LeanObject,
    mut v_msgData_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: u8 = 0;
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = 1;
    v___x_575_ = 0;
    v___x_576_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0_spec__0(v_ref_569_, v_msgData_570_, v___x_574_, v___x_575_, v___y_571_, v___y_572_);
    return v___x_576_;
}
pub unsafe fn l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0___boxed(
    mut v_ref_577_: *mut crate::leanh::LeanObject,
    mut v_msgData_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
    mut v___y_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0(v_ref_577_, v_msgData_578_, v___y_579_, v___y_580_);
    crate::leanh::lean_dec(v___y_580_);
    crate::leanh::lean_dec_ref(v___y_579_);
    crate::leanh::lean_dec(v_ref_577_);
    return v_res_582_;
}
pub unsafe fn _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_;
    v___x_587_ = l_Lean_MessageData_ofFormat(v___x_586_);
    return v___x_587_;
}
pub unsafe fn l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_(
    mut v_add_588_: *mut crate::leanh::LeanObject,
    mut v_decl_589_: *mut crate::leanh::LeanObject,
    mut v_stx_590_: *mut crate::leanh::LeanObject,
    mut v_attrKind_591_: u8,
    mut v___y_592_: *mut crate::leanh::LeanObject,
    mut v___y_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_);
    v___x_596_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__spec__0(v_stx_590_, v___x_595_, v___y_592_, v___y_593_);
    if crate::leanh::lean_obj_tag(v___x_596_) == 0 {
        let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_596_, 1);
        v___x_597_ = crate::leanh::lean_box((v_attrKind_591_) as usize);
        crate::leanh::lean_inc(v___y_593_);
        crate::leanh::lean_inc_ref(v___y_592_);
        v___x_598_ = crate::leanh::lean_apply_6(
            v_add_588_,
            v_decl_589_,
            v_stx_590_,
            v___x_597_,
            v___y_592_,
            v___y_593_,
            crate::leanh::lean_box(0),
        );
        return v___x_598_;
    } else {
        crate::leanh::lean_dec(v_stx_590_);
        crate::leanh::lean_dec(v_decl_589_);
        crate::leanh::lean_dec_ref(v_add_588_);
        return v___x_596_;
    }
}
pub unsafe fn l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2____boxed(
    mut v_add_599_: *mut crate::leanh::LeanObject,
    mut v_decl_600_: *mut crate::leanh::LeanObject,
    mut v_stx_601_: *mut crate::leanh::LeanObject,
    mut v_attrKind_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_606_: u8 = 0;
    let mut v_res_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_606_ = (crate::leanh::lean_unbox(v_attrKind_602_) as u8);
    v_res_607_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_(v_add_599_, v_decl_600_, v_stx_601_, v_attrKind_boxed_606_, v___y_603_, v___y_604_);
    crate::leanh::lean_dec(v___y_604_);
    crate::leanh::lean_dec_ref(v___y_603_);
    return v_res_607_;
}
pub unsafe fn l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_(
    mut v_erase_608_: *mut crate::leanh::LeanObject,
    mut v_decl_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_611_);
    crate::leanh::lean_inc_ref(v___y_610_);
    v___x_613_ = crate::leanh::lean_apply_4(
        v_erase_608_,
        v_decl_609_,
        v___y_610_,
        v___y_611_,
        crate::leanh::lean_box(0),
    );
    return v___x_613_;
}
pub unsafe fn l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2____boxed(
    mut v_erase_614_: *mut crate::leanh::LeanObject,
    mut v_decl_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
    mut v___y_617_: *mut crate::leanh::LeanObject,
    mut v___y_618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_619_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_(v_erase_614_, v_decl_615_, v___y_616_, v___y_617_);
    crate::leanh::lean_dec(v___y_617_);
    crate::leanh::lean_dec_ref(v___y_616_);
    return v_res_619_;
}
pub unsafe fn _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = crate::leanh::lean_unsigned_to_nat(4284851756);
    v___x_660_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_;
    v___x_661_ = l_Lean_Name_num___override(v___x_660_, v___x_659_);
    return v___x_661_;
}
pub unsafe fn _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_;
    v___x_664_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_);
    v___x_665_ = l_Lean_Name_str___override(v___x_664_, v___x_663_);
    return v___x_665_;
}
pub unsafe fn _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_667_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_;
    v___x_668_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_);
    v___x_669_ = l_Lean_Name_str___override(v___x_668_, v___x_667_);
    return v___x_669_;
}
pub unsafe fn _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_);
    v___x_672_ = l_Lean_Name_num___override(v___x_671_, v___x_670_);
    return v___x_672_;
}
pub unsafe fn l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_add_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erase_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_applicationTime_683_: u8 = 0;
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = l_Lake_testDriverAttr;
    v_attr_678_ = crate::leanh::lean_ctor_get(v___x_677_, 0);
    v_toAttributeImplCore_679_ = crate::leanh::lean_ctor_get(v_attr_678_, 0);
    v_add_680_ = crate::leanh::lean_ctor_get(v_attr_678_, 1);
    v_erase_681_ = crate::leanh::lean_ctor_get(v_attr_678_, 2);
    v_descr_682_ = crate::leanh::lean_ctor_get(v_toAttributeImplCore_679_, 2);
    v_applicationTime_683_ = crate::leanh::lean_ctor_get_uint8(
        v_toAttributeImplCore_679_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v___x_684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_);
    v___x_685_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_;
    crate::leanh::lean_inc_ref(v_add_680_);
    v___f_686_ = crate::leanh::lean_alloc_closure(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 7, 1);
    crate::leanh::lean_closure_set(v___f_686_, 0, v_add_680_);
    crate::leanh::lean_inc_ref(v_erase_681_);
    v___f_687_ = crate::leanh::lean_alloc_closure(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 1);
    crate::leanh::lean_closure_set(v___f_687_, 0, v_erase_681_);
    crate::leanh::lean_inc_ref(v_descr_682_);
    v___x_688_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_688_, 0, v___x_684_);
    crate::leanh::lean_ctor_set(v___x_688_, 1, v___x_685_);
    crate::leanh::lean_ctor_set(v___x_688_, 2, v_descr_682_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_688_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_applicationTime_683_,
    );
    v___x_689_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_688_);
    crate::leanh::lean_ctor_set(v___x_689_, 1, v___f_686_);
    crate::leanh::lean_ctor_set(v___x_689_, 2, v___f_687_);
    v___x_690_ = l_Lean_registerBuiltinAttribute(v___x_689_);
    return v___x_690_;
}
pub unsafe fn l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2____boxed(
    mut v_a_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_();
    return v_res_692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Attributes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_4284851756____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Attributes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Attributes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_AttributesCore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Attributes(builtin);
}
