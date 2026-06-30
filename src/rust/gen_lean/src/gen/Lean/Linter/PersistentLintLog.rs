// Lean compiler output
// Module: Lean.Linter.PersistentLintLog
// Imports: Lean.Environment Lean.Message Lean.Linter.Init
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_uget, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_add,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Prelude::l_Array_push___boxed;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_Environment_header, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg, runtime_initialize_Lean_Environment,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_MessageData_isLinterMessage,
    runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageData_kind, l_Lean_MessageData_toString,
    l_Lean_MessageLog_reportedPlusUnreported, runtime_initialize_Lean_Message,
};
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 105, 110, 116, 76, 111, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8071394701935581384 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8620282668294161394 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Array_push___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanCtorObject<8> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Linter_lintLogExt: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(
    mut v___y_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_313_);
    return v___y_313_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(
    mut v___y_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v___y_314_);
    leanh::lean_dec_ref(v___y_314_);
    return v_res_315_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(
    mut v_x_316_: *mut leanh::LeanObject,
    mut v_s_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_s_317_, 2);
    v___x_318_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_318_, 0, v_s_317_);
    leanh::lean_ctor_set(v___x_318_, 1, v_s_317_);
    leanh::lean_ctor_set(v___x_318_, 2, v_s_317_);
    return v___x_318_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(
    mut v_x_319_: *mut leanh::LeanObject,
    mut v_s_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_321_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v_x_319_, v_s_320_);
    leanh::lean_dec_ref(v_x_319_);
    return v_res_321_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(
    mut v_x_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = leanh::lean_box(0);
    return v___x_323_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(
    mut v_x_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v_x_324_);
    leanh::lean_dec_ref(v_x_324_);
    return v_res_325_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(
    mut v___x_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_328_, 0, v___x_326_);
    return v___x_328_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(
    mut v___x_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v___x_329_);
    return v_res_331_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(
    mut v___x_332_: *mut leanh::LeanObject,
    mut v_x_333_: *mut leanh::LeanObject,
    mut v___y_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_336_, 0, v___x_332_);
    return v___x_336_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(
    mut v___x_337_: *mut leanh::LeanObject,
    mut v_x_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
    mut v___y_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v___x_337_, v_x_338_, v___y_339_);
    leanh::lean_dec_ref(v___y_339_);
    leanh::lean_dec_ref(v_x_338_);
    return v_res_341_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_;
    v___x_373_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_372_);
    return v___x_373_;
}
pub unsafe fn l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(
    mut v_a_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_375_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_();
    return v_res_375_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_376_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(
    mut v_env_377_: *mut leanh::LeanObject,
    mut v_as_378_: *mut leanh::LeanObject,
    mut v_i_379_: *mut leanh::LeanObject,
    mut v_j_380_: *mut leanh::LeanObject,
    mut v_bs_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_383_: u8 = 0;
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: u8 = 0;
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_382_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_383_ = lean_nat_dec_eq(v_i_379_, v_zero_382_);
                if v_isZero_383_ == 1 {
                    leanh::lean_dec(v_j_380_);
                    leanh::lean_dec(v_i_379_);
                    return v_bs_381_;
                } else {
                    v___x_384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0);
                    v_one_385_ = leanh::lean_unsigned_to_nat(1);
                    v_n_386_ = lean_nat_sub(v_i_379_, v_one_385_);
                    leanh::lean_dec(v_i_379_);
                    v___x_387_ = lean_array_fget_borrowed(v_as_378_, v_j_380_);
                    v___x_388_ = l_Lean_Linter_lintLogExt;
                    v___x_389_ = 0;
                    v___x_390_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                        v___x_384_, v___x_388_, v_env_377_, v_j_380_, v___x_389_,
                    );
                    leanh::lean_inc(v___x_387_);
                    v___x_391_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_391_, 0, v___x_387_);
                    leanh::lean_ctor_set(v___x_391_, 1, v___x_390_);
                    v___x_392_ = lean_nat_add(v_j_380_, v_one_385_);
                    leanh::lean_dec(v_j_380_);
                    v___x_393_ = lean_array_push(v_bs_381_, v___x_391_);
                    v_i_379_ = v_n_386_;
                    v_j_380_ = v___x_392_;
                    v_bs_381_ = v___x_393_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___boxed(
    mut v_env_395_: *mut leanh::LeanObject,
    mut v_as_396_: *mut leanh::LeanObject,
    mut v_i_397_: *mut leanh::LeanObject,
    mut v_j_398_: *mut leanh::LeanObject,
    mut v_bs_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(
        v_env_395_, v_as_396_, v_i_397_, v_j_398_, v_bs_399_,
    );
    leanh::lean_dec_ref(v_as_396_);
    leanh::lean_dec_ref(v_env_395_);
    return v_res_400_;
}
pub unsafe fn l_Lean_Linter_getAllLints(
    mut v_env_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Environment_header(v_env_401_);
    v___x_403_ = l_Lean_EnvironmentHeader_moduleNames(v___x_402_);
    v___x_404_ = lean_array_get_size(v___x_403_);
    v___x_405_ = leanh::lean_unsigned_to_nat(0);
    v___x_406_ = lean_mk_empty_array_with_capacity(v___x_404_);
    v___x_407_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(
        v_env_401_, v___x_403_, v___x_404_, v___x_405_, v___x_406_,
    );
    leanh::lean_dec_ref(v___x_403_);
    return v___x_407_;
}
pub unsafe fn l_Lean_Linter_getAllLints___boxed(
    mut v_env_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Lean_Linter_getAllLints(v_env_408_);
    leanh::lean_dec_ref(v_env_408_);
    return v_res_409_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0(
    mut v_env_410_: *mut leanh::LeanObject,
    mut v_as_411_: *mut leanh::LeanObject,
    mut v_i_412_: *mut leanh::LeanObject,
    mut v_j_413_: *mut leanh::LeanObject,
    mut v_inv_414_: *mut leanh::LeanObject,
    mut v_bs_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(
        v_env_410_, v_as_411_, v_i_412_, v_j_413_, v_bs_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___boxed(
    mut v_env_417_: *mut leanh::LeanObject,
    mut v_as_418_: *mut leanh::LeanObject,
    mut v_i_419_: *mut leanh::LeanObject,
    mut v_j_420_: *mut leanh::LeanObject,
    mut v_inv_421_: *mut leanh::LeanObject,
    mut v_bs_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0(
        v_env_417_, v_as_418_, v_i_419_, v_j_420_, v_inv_421_, v_bs_422_,
    );
    leanh::lean_dec_ref(v_as_418_);
    leanh::lean_dec_ref(v_env_417_);
    return v_res_423_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(
    mut v_as_424_: *mut leanh::LeanObject,
    mut v_i_425_: usize,
    mut v_stop_426_: usize,
    mut v_b_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: usize = 0;
    let mut v___x_432_: usize = 0;
    let mut v___x_434_: u8 = 0;
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keepFullRange_439_: u8 = 0;
    let mut v_severity_440_: u8 = 0;
    let mut v_isSilent_441_: u8 = 0;
    let mut v_caption_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_447_: u8 = 0;
    let mut v_kind_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: u8 = 0;
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_434_ = lean_usize_dec_eq(v_i_425_, v_stop_426_);
                if v___x_434_ == 0 {
                    v___x_435_ = lean_array_uget(v_as_424_, v_i_425_);
                    v_fileName_436_ = leanh::lean_ctor_get(v___x_435_, 0);
                    v_pos_437_ = leanh::lean_ctor_get(v___x_435_, 1);
                    v_endPos_438_ = leanh::lean_ctor_get(v___x_435_, 2);
                    v_keepFullRange_439_ = leanh::lean_ctor_get_uint8(
                        v___x_435_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v_severity_440_ = leanh::lean_ctor_get_uint8(
                        v___x_435_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSilent_441_ = leanh::lean_ctor_get_uint8(
                        v___x_435_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    );
                    v_caption_442_ = leanh::lean_ctor_get(v___x_435_, 3);
                    v_data_443_ = leanh::lean_ctor_get(v___x_435_, 4);
                    v_isSharedCheck_461_ = (!leanh::lean_is_exclusive(v___x_435_)) as u8;
                    if v_isSharedCheck_461_ == 0 {
                        v___x_445_ = v___x_435_;
                        v_isShared_446_ = v_isSharedCheck_461_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_data_443_);
                        leanh::lean_inc(v_caption_442_);
                        leanh::lean_inc(v_endPos_438_);
                        leanh::lean_inc(v_pos_437_);
                        leanh::lean_inc(v_fileName_436_);
                        leanh::lean_dec(v___x_435_);
                        v___x_445_ = leanh::lean_box(0);
                        v_isShared_446_ = v_isSharedCheck_461_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_b_427_;
                }
            }
            1 => {
                v___x_431_ = 1usize;
                v___x_432_ = lean_usize_add(v_i_425_, v___x_431_);
                v_i_425_ = v___x_432_;
                v_b_427_ = v_val_430_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v_data_443_);
                v___x_447_ = l_Lean_MessageData_isLinterMessage(v_data_443_);
                if v___x_447_ == 0 {
                    leanh::lean_del_object(v___x_445_);
                    leanh::lean_dec(v_data_443_);
                    leanh::lean_dec_ref(v_caption_442_);
                    leanh::lean_dec(v_endPos_438_);
                    leanh::lean_dec_ref(v_pos_437_);
                    leanh::lean_dec_ref(v_fileName_436_);
                    v_val_430_ = v_b_427_;
                    state = 1;
                    continue;
                } else {
                    v_kind_448_ = l_Lean_MessageData_kind(v_data_443_);
                    v___x_449_ = l_Lean_Name_isAnonymous(v_kind_448_);
                    if v___x_449_ == 0 {
                        v___x_450_ = l_Lean_MessageData_toString(v_data_443_);
                        v___x_451_ = l_Lean_Linter_lintLogExt;
                        v_toEnvExtension_452_ = leanh::lean_ctor_get(v___x_451_, 0);
                        v_asyncMode_453_ = leanh::lean_ctor_get(v_toEnvExtension_452_, 2);
                        if v_isShared_446_ == 0 {
                            leanh::lean_ctor_set(v___x_445_, 4, v___x_450_);
                            v___x_455_ = v___x_445_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_460_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fileName_436_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_460_, 1, v_pos_437_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_460_, 2, v_endPos_438_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_460_, 3, v_caption_442_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_460_, 4, v___x_450_);
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_460_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                                v_keepFullRange_439_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_460_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1)
                                    as u32,
                                v_severity_440_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_460_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2)
                                    as u32,
                                v_isSilent_441_,
                            );
                            v___x_455_ = v_reuseFailAlloc_460_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_kind_448_);
                        leanh::lean_del_object(v___x_445_);
                        leanh::lean_dec(v_data_443_);
                        leanh::lean_dec_ref(v_caption_442_);
                        leanh::lean_dec(v_endPos_438_);
                        leanh::lean_dec_ref(v_pos_437_);
                        leanh::lean_dec_ref(v_fileName_436_);
                        v_val_430_ = v_b_427_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_kind_448_);
                v___x_456_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_456_, 0, v___x_455_);
                leanh::lean_ctor_set(v___x_456_, 1, v_kind_448_);
                v___x_457_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_457_, 0, v_kind_448_);
                leanh::lean_ctor_set(v___x_457_, 1, v___x_456_);
                v___x_458_ = leanh::lean_box(0);
                v___x_459_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_451_,
                    v_b_427_,
                    v___x_457_,
                    v_asyncMode_453_,
                    v___x_458_,
                );
                v_val_430_ = v___x_459_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1___boxed(
    mut v_as_462_: *mut leanh::LeanObject,
    mut v_i_463_: *mut leanh::LeanObject,
    mut v_stop_464_: *mut leanh::LeanObject,
    mut v_b_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_467_: usize = 0;
    let mut v_stop_boxed_468_: usize = 0;
    let mut v_res_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_467_ = leanh::lean_unbox_usize(v_i_463_);
    leanh::lean_dec(v_i_463_);
    v_stop_boxed_468_ = leanh::lean_unbox_usize(v_stop_464_);
    leanh::lean_dec(v_stop_464_);
    v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_as_462_, v_i_boxed_467_, v_stop_boxed_468_, v_b_465_);
    leanh::lean_dec_ref(v_as_462_);
    return v_res_469_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(
    mut v_x_470_: *mut leanh::LeanObject,
    mut v_x_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_470_) == 0 {
        let mut v_cs_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_476_: u8 = 0;
        v_cs_473_ = leanh::lean_ctor_get(v_x_470_, 0);
        v___x_474_ = leanh::lean_unsigned_to_nat(0);
        v___x_475_ = lean_array_get_size(v_cs_473_);
        v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
        if v___x_476_ == 0 {
            return v_x_471_;
        } else {
            let mut v___x_477_: u8 = 0;
            v___x_477_ = lean_nat_dec_le(v___x_475_, v___x_475_);
            if v___x_477_ == 0 {
                if v___x_476_ == 0 {
                    return v_x_471_;
                } else {
                    let mut v___x_478_: usize = 0;
                    let mut v___x_479_: usize = 0;
                    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_478_ = 0usize;
                    v___x_479_ = lean_usize_of_nat(v___x_475_);
                    v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_473_, v___x_478_, v___x_479_, v_x_471_);
                    return v___x_480_;
                }
            } else {
                let mut v___x_481_: usize = 0;
                let mut v___x_482_: usize = 0;
                let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_481_ = 0usize;
                v___x_482_ = lean_usize_of_nat(v___x_475_);
                v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_473_, v___x_481_, v___x_482_, v_x_471_);
                return v___x_483_;
            }
        }
    } else {
        let mut v_vs_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: u8 = 0;
        v_vs_484_ = leanh::lean_ctor_get(v_x_470_, 0);
        v___x_485_ = leanh::lean_unsigned_to_nat(0);
        v___x_486_ = lean_array_get_size(v_vs_484_);
        v___x_487_ = lean_nat_dec_lt(v___x_485_, v___x_486_);
        if v___x_487_ == 0 {
            return v_x_471_;
        } else {
            let mut v___x_488_: u8 = 0;
            v___x_488_ = lean_nat_dec_le(v___x_486_, v___x_486_);
            if v___x_488_ == 0 {
                if v___x_487_ == 0 {
                    return v_x_471_;
                } else {
                    let mut v___x_489_: usize = 0;
                    let mut v___x_490_: usize = 0;
                    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_489_ = 0usize;
                    v___x_490_ = lean_usize_of_nat(v___x_486_);
                    v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_484_, v___x_489_, v___x_490_, v_x_471_);
                    return v___x_491_;
                }
            } else {
                let mut v___x_492_: usize = 0;
                let mut v___x_493_: usize = 0;
                let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_492_ = 0usize;
                v___x_493_ = lean_usize_of_nat(v___x_486_);
                v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_484_, v___x_492_, v___x_493_, v_x_471_);
                return v___x_494_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(
    mut v_as_495_: *mut leanh::LeanObject,
    mut v_i_496_: usize,
    mut v_stop_497_: usize,
    mut v_b_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: usize = 0;
    let mut v___x_504_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_500_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
                if v___x_500_ == 0 {
                    v___x_501_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
                    v___x_502_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___x_501_, v_b_498_);
                    v___x_503_ = 1usize;
                    v___x_504_ = lean_usize_add(v_i_496_, v___x_503_);
                    v_i_496_ = v___x_504_;
                    v_b_498_ = v___x_502_;
                    state = 0;
                    continue;
                } else {
                    return v_b_498_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1___boxed(
    mut v_as_506_: *mut leanh::LeanObject,
    mut v_i_507_: *mut leanh::LeanObject,
    mut v_stop_508_: *mut leanh::LeanObject,
    mut v_b_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_511_: usize = 0;
    let mut v_stop_boxed_512_: usize = 0;
    let mut v_res_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_511_ = leanh::lean_unbox_usize(v_i_507_);
    leanh::lean_dec(v_i_507_);
    v_stop_boxed_512_ = leanh::lean_unbox_usize(v_stop_508_);
    leanh::lean_dec(v_stop_508_);
    v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_as_506_, v_i_boxed_511_, v_stop_boxed_512_, v_b_509_);
    leanh::lean_dec_ref(v_as_506_);
    return v_res_513_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2___boxed(
    mut v_x_514_: *mut leanh::LeanObject,
    mut v_x_515_: *mut leanh::LeanObject,
    mut v___y_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_517_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v_x_514_, v_x_515_);
    leanh::lean_dec_ref(v_x_514_);
    return v_res_517_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_518_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(
    mut v_x_519_: *mut leanh::LeanObject,
    mut v_x_520_: usize,
    mut v_x_521_: usize,
    mut v_x_522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_519_) == 0 {
        let mut v_cs_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: usize = 0;
        let mut v_j_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_529_: usize = 0;
        let mut v___x_530_: usize = 0;
        let mut v___x_531_: usize = 0;
        let mut v___x_532_: usize = 0;
        let mut v___x_533_: usize = 0;
        let mut v___x_534_: usize = 0;
        let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: u8 = 0;
        v_cs_524_ = leanh::lean_ctor_get(v_x_519_, 0);
        v___x_525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0);
        v___x_526_ = lean_usize_shift_right(v_x_520_, v_x_521_);
        v_j_527_ = lean_usize_to_nat(v___x_526_);
        v___x_528_ = lean_array_get_borrowed(v___x_525_, v_cs_524_, v_j_527_);
        v___x_529_ = 1usize;
        v___x_530_ = lean_usize_shift_left(v___x_529_, v_x_521_);
        v___x_531_ = lean_usize_sub(v___x_530_, v___x_529_);
        v___x_532_ = lean_usize_land(v_x_520_, v___x_531_);
        v___x_533_ = 5usize;
        v___x_534_ = lean_usize_sub(v_x_521_, v___x_533_);
        v___x_535_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___x_528_, v___x_532_, v___x_534_, v_x_522_);
        v___x_536_ = leanh::lean_unsigned_to_nat(1);
        v___x_537_ = lean_nat_add(v_j_527_, v___x_536_);
        leanh::lean_dec(v_j_527_);
        v___x_538_ = lean_array_get_size(v_cs_524_);
        v___x_539_ = lean_nat_dec_lt(v___x_537_, v___x_538_);
        if v___x_539_ == 0 {
            leanh::lean_dec(v___x_537_);
            return v___x_535_;
        } else {
            let mut v___x_540_: u8 = 0;
            v___x_540_ = lean_nat_dec_le(v___x_538_, v___x_538_);
            if v___x_540_ == 0 {
                if v___x_539_ == 0 {
                    leanh::lean_dec(v___x_537_);
                    return v___x_535_;
                } else {
                    let mut v___x_541_: usize = 0;
                    let mut v___x_542_: usize = 0;
                    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_541_ = lean_usize_of_nat(v___x_537_);
                    leanh::lean_dec(v___x_537_);
                    v___x_542_ = lean_usize_of_nat(v___x_538_);
                    v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_524_, v___x_541_, v___x_542_, v___x_535_);
                    return v___x_543_;
                }
            } else {
                let mut v___x_544_: usize = 0;
                let mut v___x_545_: usize = 0;
                let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_544_ = lean_usize_of_nat(v___x_537_);
                leanh::lean_dec(v___x_537_);
                v___x_545_ = lean_usize_of_nat(v___x_538_);
                v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_524_, v___x_544_, v___x_545_, v___x_535_);
                return v___x_546_;
            }
        }
    } else {
        let mut v_vs_547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_550_: u8 = 0;
        v_vs_547_ = leanh::lean_ctor_get(v_x_519_, 0);
        v___x_548_ = lean_usize_to_nat(v_x_520_);
        v___x_549_ = lean_array_get_size(v_vs_547_);
        v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
        if v___x_550_ == 0 {
            leanh::lean_dec(v___x_548_);
            return v_x_522_;
        } else {
            let mut v___x_551_: u8 = 0;
            v___x_551_ = lean_nat_dec_le(v___x_549_, v___x_549_);
            if v___x_551_ == 0 {
                if v___x_550_ == 0 {
                    leanh::lean_dec(v___x_548_);
                    return v_x_522_;
                } else {
                    let mut v___x_552_: usize = 0;
                    let mut v___x_553_: usize = 0;
                    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_552_ = lean_usize_of_nat(v___x_548_);
                    leanh::lean_dec(v___x_548_);
                    v___x_553_ = lean_usize_of_nat(v___x_549_);
                    v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_547_, v___x_552_, v___x_553_, v_x_522_);
                    return v___x_554_;
                }
            } else {
                let mut v___x_555_: usize = 0;
                let mut v___x_556_: usize = 0;
                let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_555_ = lean_usize_of_nat(v___x_548_);
                leanh::lean_dec(v___x_548_);
                v___x_556_ = lean_usize_of_nat(v___x_549_);
                v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_547_, v___x_555_, v___x_556_, v_x_522_);
                return v___x_557_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___boxed(
    mut v_x_558_: *mut leanh::LeanObject,
    mut v_x_559_: *mut leanh::LeanObject,
    mut v_x_560_: *mut leanh::LeanObject,
    mut v_x_561_: *mut leanh::LeanObject,
    mut v___y_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1520__boxed_563_: usize = 0;
    let mut v_x_1521__boxed_564_: usize = 0;
    let mut v_res_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1520__boxed_563_ = leanh::lean_unbox_usize(v_x_559_);
    leanh::lean_dec(v_x_559_);
    v_x_1521__boxed_564_ = leanh::lean_unbox_usize(v_x_560_);
    leanh::lean_dec(v_x_560_);
    v_res_565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v_x_558_, v_x_1520__boxed_563_, v_x_1521__boxed_564_, v_x_561_);
    leanh::lean_dec_ref(v_x_558_);
    return v_res_565_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(
    mut v_t_566_: *mut leanh::LeanObject,
    mut v_init_567_: *mut leanh::LeanObject,
    mut v_start_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: u8 = 0;
    v___x_570_ = leanh::lean_unsigned_to_nat(0);
    v___x_571_ = lean_nat_dec_eq(v_start_568_, v___x_570_);
    if v___x_571_ == 0 {
        let mut v_root_572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_574_: usize = 0;
        let mut v_tailOff_575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_576_: u8 = 0;
        v_root_572_ = leanh::lean_ctor_get(v_t_566_, 0);
        v_tail_573_ = leanh::lean_ctor_get(v_t_566_, 1);
        v_shift_574_ = leanh::lean_ctor_get_usize(v_t_566_, 4);
        v_tailOff_575_ = leanh::lean_ctor_get(v_t_566_, 3);
        v___x_576_ = lean_nat_dec_le(v_tailOff_575_, v_start_568_);
        if v___x_576_ == 0 {
            let mut v___x_577_: usize = 0;
            let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_580_: u8 = 0;
            v___x_577_ = lean_usize_of_nat(v_start_568_);
            v___x_578_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v_root_572_, v___x_577_, v_shift_574_, v_init_567_);
            v___x_579_ = lean_array_get_size(v_tail_573_);
            v___x_580_ = lean_nat_dec_lt(v___x_570_, v___x_579_);
            if v___x_580_ == 0 {
                return v___x_578_;
            } else {
                let mut v___x_581_: u8 = 0;
                v___x_581_ = lean_nat_dec_le(v___x_579_, v___x_579_);
                if v___x_581_ == 0 {
                    if v___x_580_ == 0 {
                        return v___x_578_;
                    } else {
                        let mut v___x_582_: usize = 0;
                        let mut v___x_583_: usize = 0;
                        let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_582_ = 0usize;
                        v___x_583_ = lean_usize_of_nat(v___x_579_);
                        v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_573_, v___x_582_, v___x_583_, v___x_578_);
                        return v___x_584_;
                    }
                } else {
                    let mut v___x_585_: usize = 0;
                    let mut v___x_586_: usize = 0;
                    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_585_ = 0usize;
                    v___x_586_ = lean_usize_of_nat(v___x_579_);
                    v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_573_, v___x_585_, v___x_586_, v___x_578_);
                    return v___x_587_;
                }
            }
        } else {
            let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_590_: u8 = 0;
            v___x_588_ = lean_nat_sub(v_start_568_, v_tailOff_575_);
            v___x_589_ = lean_array_get_size(v_tail_573_);
            v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
            if v___x_590_ == 0 {
                leanh::lean_dec(v___x_588_);
                return v_init_567_;
            } else {
                let mut v___x_591_: u8 = 0;
                v___x_591_ = lean_nat_dec_le(v___x_589_, v___x_589_);
                if v___x_591_ == 0 {
                    if v___x_590_ == 0 {
                        leanh::lean_dec(v___x_588_);
                        return v_init_567_;
                    } else {
                        let mut v___x_592_: usize = 0;
                        let mut v___x_593_: usize = 0;
                        let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_592_ = lean_usize_of_nat(v___x_588_);
                        leanh::lean_dec(v___x_588_);
                        v___x_593_ = lean_usize_of_nat(v___x_589_);
                        v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_573_, v___x_592_, v___x_593_, v_init_567_);
                        return v___x_594_;
                    }
                } else {
                    let mut v___x_595_: usize = 0;
                    let mut v___x_596_: usize = 0;
                    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_595_ = lean_usize_of_nat(v___x_588_);
                    leanh::lean_dec(v___x_588_);
                    v___x_596_ = lean_usize_of_nat(v___x_589_);
                    v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_573_, v___x_595_, v___x_596_, v_init_567_);
                    return v___x_597_;
                }
            }
        }
    } else {
        let mut v_root_598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: u8 = 0;
        v_root_598_ = leanh::lean_ctor_get(v_t_566_, 0);
        v_tail_599_ = leanh::lean_ctor_get(v_t_566_, 1);
        v___x_600_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v_root_598_, v_init_567_);
        v___x_601_ = lean_array_get_size(v_tail_599_);
        v___x_602_ = lean_nat_dec_lt(v___x_570_, v___x_601_);
        if v___x_602_ == 0 {
            return v___x_600_;
        } else {
            let mut v___x_603_: u8 = 0;
            v___x_603_ = lean_nat_dec_le(v___x_601_, v___x_601_);
            if v___x_603_ == 0 {
                if v___x_602_ == 0 {
                    return v___x_600_;
                } else {
                    let mut v___x_604_: usize = 0;
                    let mut v___x_605_: usize = 0;
                    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_604_ = 0usize;
                    v___x_605_ = lean_usize_of_nat(v___x_601_);
                    v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_599_, v___x_604_, v___x_605_, v___x_600_);
                    return v___x_606_;
                }
            } else {
                let mut v___x_607_: usize = 0;
                let mut v___x_608_: usize = 0;
                let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_607_ = 0usize;
                v___x_608_ = lean_usize_of_nat(v___x_601_);
                v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_599_, v___x_607_, v___x_608_, v___x_600_);
                return v___x_609_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0___boxed(
    mut v_t_610_: *mut leanh::LeanObject,
    mut v_init_611_: *mut leanh::LeanObject,
    mut v_start_612_: *mut leanh::LeanObject,
    mut v___y_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_614_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(
        v_t_610_,
        v_init_611_,
        v_start_612_,
    );
    leanh::lean_dec(v_start_612_);
    leanh::lean_dec_ref(v_t_610_);
    return v_res_614_;
}
pub unsafe fn l_Lean_Linter_recordLints(
    mut v_env_615_: *mut leanh::LeanObject,
    mut v_messages_616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_616_);
    v___x_619_ = leanh::lean_unsigned_to_nat(0);
    v___x_620_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(
        v___x_618_, v_env_615_, v___x_619_,
    );
    leanh::lean_dec_ref(v___x_618_);
    return v___x_620_;
}
pub unsafe fn l_Lean_Linter_recordLints___boxed(
    mut v_env_621_: *mut leanh::LeanObject,
    mut v_messages_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Lean_Linter_recordLints(v_env_621_, v_messages_622_);
    return v_res_624_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_PersistentLintLog(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_lintLogExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Linter_lintLogExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_PersistentLintLog(
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
pub unsafe fn initialize_Lean_Linter_PersistentLintLog(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_PersistentLintLog(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_PersistentLintLog(builtin);
}