// Lean compiler output
// Module: Lean.Compiler.ExportAttr
// Imports: Lean.Attributes
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_string_is_valid_pos, lean_string_utf8_byte_size, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::Defs::l_String_instInhabitedSlice;
use crate::r#gen::Init::Data::String::Substring::l_Substring_Raw_nextn;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_Attribute_Builtin_getId,
    l_Lean_ParametricAttribute_getParam_x3f___redArg, l_Lean_registerParametricAttribute___redArg,
    runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 101, 120, 112, 111, 114, 116, 96, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 58, 32, 96, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 118, 97, 108, 105, 100, 32, 67, 43, 43, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 112, 111, 114, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7105627033797813609 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 112, 111, 114, 116, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16297951122169862591 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [110, 97, 109, 101, 32, 116, 111, 32, 98, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 111, 114, 115, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_exportAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value: leanh::LeanStringObject<607> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 607, m_capacity: 607, m_length: 606, m_data: [69, 120, 112, 111, 114, 116, 115, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 117, 110, 100, 101, 114, 32, 116, 104, 101, 32, 112, 114, 111, 118, 105, 100, 101, 100, 32, 117, 110, 109, 97, 110, 103, 108, 101, 100, 32, 115, 121, 109, 98, 111, 108, 32, 110, 97, 109, 101, 46, 32, 84, 104, 105, 115, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 114, 101, 102, 101, 114, 32, 116, 111, 32, 76, 101, 97, 110, 10, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 102, 114, 111, 109, 32, 111, 116, 104, 101, 114, 32, 112, 114, 111, 103, 114, 97, 109, 109, 105, 110, 103, 32, 108, 97, 110, 103, 117, 97, 103, 101, 115, 32, 108, 105, 107, 101, 32, 67, 46, 10, 10, 69, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 64, 91, 101, 120, 112, 111, 114, 116, 32, 108, 101, 97, 110, 95, 99, 111, 108, 111, 114, 95, 102, 114, 111, 109, 95, 109, 97, 112, 93, 10, 100, 101, 102, 32, 99, 111, 108, 111, 114, 86, 97, 108, 117, 101, 32, 40, 112, 114, 111, 112, 101, 114, 116, 105, 101, 115, 32, 58, 32, 64, 38, 32, 83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 32, 83, 116, 114, 105, 110, 103, 32, 83, 116, 114, 105, 110, 103, 41, 32, 58, 32, 85, 73, 110, 116, 51, 50, 32, 58, 61, 10, 32, 32, 109, 97, 116, 99, 104, 32, 112, 114, 111, 112, 101, 114, 116, 105, 101, 115, 91, 34, 99, 111, 108, 111, 114, 34, 93, 63, 32, 119, 105, 116, 104, 10, 32, 32, 124, 32, 115, 111, 109, 101, 32, 34, 114, 101, 100, 34, 32, 61, 62, 32, 48, 120, 102, 102, 48, 48, 48, 48, 10, 32, 32, 124, 32, 115, 111, 109, 101, 32, 34, 103, 114, 101, 101, 110, 34, 32, 61, 62, 32, 48, 120, 48, 48, 102, 102, 48, 48, 10, 32, 32, 124, 32, 115, 111, 109, 101, 32, 34, 98, 108, 117, 101, 34, 32, 61, 62, 32, 48, 120, 48, 48, 48, 48, 102, 102, 10, 32, 32, 124, 32, 95, 32, 61, 62, 32, 45, 49, 10, 96, 96, 96, 10, 82, 117, 115, 116, 32, 99, 111, 100, 101, 32, 99, 97, 110, 32, 105, 109, 112, 111, 114, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 76, 101, 97, 110, 32, 99, 114, 97, 116, 101, 32, 97, 110, 100, 32, 99, 97, 108, 108, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 82, 117, 115, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 100, 105, 114, 101, 99, 116, 108, 121, 46, 10, 10, 84, 104, 101, 32, 111, 112, 112, 111, 115, 105, 116, 101, 32, 111, 102, 32, 116, 104, 105, 115, 32, 105, 115, 32, 96, 64, 91, 101, 120, 116, 101, 114, 110, 93, 96, 44, 32, 119, 104, 105, 99, 104, 32, 97, 108, 108, 111, 119, 115, 32, 76, 101, 97, 110, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 116, 111, 32, 114, 101, 102, 101, 114, 32, 116, 111, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 102, 114, 111, 109, 32, 111, 116, 104, 101, 114, 10, 112, 114, 111, 103, 114, 97, 109, 109, 105, 110, 103, 32, 108, 97, 110, 103, 117, 97, 103, 101, 115, 46, 10, 0]};
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 53 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 29 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 29 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_isExport___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [109, 97, 105, 110, 0],
    };
static mut l_Lean_isExport___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isExport___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_isExport___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_isExport___closed__0_value) as *mut leanh::LeanObject,
            771961157887135399 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_isExport___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isExport___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(
    mut v_msg_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = l_String_instInhabitedSlice;
    v___x_325_ = lean_panic_fn_borrowed(v___x_324_, v_msg_323_);
    return v___x_325_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(
    mut v_s_326_: *mut leanh::LeanObject,
    mut v_pos_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: u8 = 0;
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u8 = 0;
    let mut v___x_341_: u32 = 0;
    let mut v___y_343_: u8 = 0;
    let mut v___x_344_: u32 = 0;
    let mut v___x_345_: u8 = 0;
    let mut v___y_347_: u8 = 0;
    let mut v___x_348_: u32 = 0;
    let mut v___x_349_: u8 = 0;
    let mut v___x_350_: u32 = 0;
    let mut v___x_351_: u8 = 0;
    let mut v___x_353_: u32 = 0;
    let mut v___x_354_: u8 = 0;
    let mut v___x_355_: u32 = 0;
    let mut v___x_356_: u8 = 0;
    let mut v___x_357_: u32 = 0;
    let mut v___x_358_: u8 = 0;
    let mut v___x_359_: u32 = 0;
    let mut v___x_360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_328_ = leanh::lean_ctor_get(v_s_326_, 0);
                v_startInclusive_329_ = leanh::lean_ctor_get(v_s_326_, 1);
                v_endExclusive_330_ = leanh::lean_ctor_get(v_s_326_, 2);
                v___x_331_ = lean_nat_add(v_startInclusive_329_, v_pos_327_);
                v___x_338_ = leanh::lean_unsigned_to_nat(0);
                v___x_339_ = lean_nat_sub(v_endExclusive_330_, v___x_331_);
                v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
                leanh::lean_dec(v___x_339_);
                if v___x_340_ == 0 {
                    v___x_341_ = lean_string_utf8_get_fast(v_str_328_, v___x_331_);
                    v___x_357_ = 65;
                    v___x_358_ = lean_uint32_dec_le(v___x_357_, v___x_341_);
                    if v___x_358_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        v___x_359_ = 90;
                        v___x_360_ = lean_uint32_dec_le(v___x_341_, v___x_359_);
                        if v___x_360_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_331_);
                    return v_pos_327_;
                }
            }
            1 => {
                v___x_333_ = lean_string_utf8_next_fast(v_str_328_, v___x_331_);
                v___x_334_ = lean_nat_sub(v___x_333_, v___x_331_);
                leanh::lean_dec(v___x_331_);
                v___x_335_ = lean_nat_add(v_pos_327_, v___x_334_);
                leanh::lean_dec(v___x_334_);
                v___x_336_ = lean_nat_dec_lt(v_pos_327_, v___x_335_);
                if v___x_336_ == 0 {
                    leanh::lean_dec(v___x_335_);
                    return v_pos_327_;
                } else {
                    leanh::lean_dec(v_pos_327_);
                    v_pos_327_ = v___x_335_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_343_ == 0 {
                    v___x_344_ = 95;
                    v___x_345_ = lean_uint32_dec_eq(v___x_341_, v___x_344_);
                    if v___x_345_ == 0 {
                        leanh::lean_dec(v___x_331_);
                        return v_pos_327_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_347_ == 0 {
                    v___x_348_ = 48;
                    v___x_349_ = lean_uint32_dec_le(v___x_348_, v___x_341_);
                    if v___x_349_ == 0 {
                        v___y_343_ = v___x_349_;
                        state = 2;
                        continue;
                    } else {
                        v___x_350_ = 57;
                        v___x_351_ = lean_uint32_dec_le(v___x_341_, v___x_350_);
                        v___y_343_ = v___x_351_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_353_ = 97;
                v___x_354_ = lean_uint32_dec_le(v___x_353_, v___x_341_);
                if v___x_354_ == 0 {
                    v___y_347_ = v___x_354_;
                    state = 3;
                    continue;
                } else {
                    v___x_355_ = 122;
                    v___x_356_ = lean_uint32_dec_le(v___x_341_, v___x_355_);
                    v___y_347_ = v___x_356_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0___boxed(
    mut v_s_361_: *mut leanh::LeanObject,
    mut v_pos_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_363_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v_s_361_, v_pos_362_);
    leanh::lean_dec_ref(v_s_361_);
    return v_res_363_;
}
pub unsafe fn _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__2;
    v___x_368_ = leanh::lean_unsigned_to_nat(14);
    v___x_369_ = leanh::lean_unsigned_to_nat(22);
    v___x_370_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__1;
    v___x_371_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__0;
    v___x_372_ =
        l_mkPanicMessageWithDecl(v___x_371_, v___x_370_, v___x_369_, v___x_368_, v___x_367_);
    return v___x_372_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(
    mut v_id_373_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: u8 = 0;
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: u8 = 0;
    let mut v___x_394_: u8 = 0;
    let mut v___x_395_: u8 = 0;
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_398_: u8 = 0;
    let mut v___y_400_: u32 = 0;
    let mut v___x_401_: u32 = 0;
    let mut v___x_402_: u8 = 0;
    let mut v___x_403_: u32 = 0;
    let mut v___x_404_: u8 = 0;
    let mut v___y_406_: u32 = 0;
    let mut v___x_407_: u32 = 0;
    let mut v___x_408_: u8 = 0;
    let mut v___x_409_: u32 = 0;
    let mut v___x_410_: u8 = 0;
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u32 = 0;
    let mut v_val_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_411_ = leanh::lean_unsigned_to_nat(0);
                v___x_412_ = lean_string_utf8_byte_size(v_id_373_);
                leanh::lean_inc_ref(v_id_373_);
                v___x_413_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_413_, 0, v_id_373_);
                leanh::lean_ctor_set(v___x_413_, 1, v___x_411_);
                leanh::lean_ctor_set(v___x_413_, 2, v___x_412_);
                v___x_414_ = l_String_Slice_Pos_get_x3f(v___x_413_, v___x_411_);
                leanh::lean_dec_ref_known(v___x_413_, 3);
                if leanh::lean_obj_tag(v___x_414_) == 0 {
                    v___x_415_ = 65;
                    v___y_406_ = v___x_415_;
                    state = 6;
                    continue;
                } else {
                    v_val_416_ = leanh::lean_ctor_get(v___x_414_, 0);
                    leanh::lean_inc(v_val_416_);
                    leanh::lean_dec_ref_known(v___x_414_, 1);
                    v___x_417_ = leanh::lean_unbox_uint32(v_val_416_);
                    leanh::lean_dec(v_val_416_);
                    v___y_406_ = v___x_417_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_378_ = leanh::lean_unsigned_to_nat(0);
                v___x_379_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__0(v___y_375_, v___x_378_);
                leanh::lean_dec_ref(v___y_375_);
                v___x_380_ = lean_nat_sub(v_endExclusive_377_, v_startInclusive_376_);
                leanh::lean_dec(v_startInclusive_376_);
                leanh::lean_dec(v_endExclusive_377_);
                v___x_381_ = lean_nat_dec_eq(v___x_379_, v___x_380_);
                leanh::lean_dec(v___x_380_);
                leanh::lean_dec(v___x_379_);
                return v___x_381_;
            }
            2 => {
                v___x_383_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3_once
                    ),
                    _init_l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___closed__3,
                );
                v___x_384_ = l_panic___at___00__private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId_spec__1(v___x_383_);
                v_startInclusive_385_ = leanh::lean_ctor_get(v___x_384_, 1);
                leanh::lean_inc(v_startInclusive_385_);
                v_endExclusive_386_ = leanh::lean_ctor_get(v___x_384_, 2);
                leanh::lean_inc(v_endExclusive_386_);
                v___y_375_ = v___x_384_;
                v_startInclusive_376_ = v_startInclusive_385_;
                v_endExclusive_377_ = v_endExclusive_386_;
                state = 1;
                continue;
            }
            3 => {
                v___x_388_ = leanh::lean_unsigned_to_nat(0);
                v___x_389_ = lean_string_utf8_byte_size(v_id_373_);
                leanh::lean_inc_ref(v_id_373_);
                v___x_390_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_390_, 0, v_id_373_);
                leanh::lean_ctor_set(v___x_390_, 1, v___x_388_);
                leanh::lean_ctor_set(v___x_390_, 2, v___x_389_);
                v___x_391_ = leanh::lean_unsigned_to_nat(1);
                v___x_392_ = l_Substring_Raw_nextn(v___x_390_, v___x_391_, v___x_388_);
                leanh::lean_dec_ref_known(v___x_390_, 3);
                v___x_393_ = lean_string_is_valid_pos(v_id_373_, v___x_392_);
                if v___x_393_ == 0 {
                    leanh::lean_dec(v___x_392_);
                    leanh::lean_dec_ref(v_id_373_);
                    state = 2;
                    continue;
                } else {
                    v___x_394_ = lean_string_is_valid_pos(v_id_373_, v___x_389_);
                    if v___x_394_ == 0 {
                        leanh::lean_dec(v___x_392_);
                        leanh::lean_dec_ref(v_id_373_);
                        state = 2;
                        continue;
                    } else {
                        v___x_395_ = lean_nat_dec_le(v___x_392_, v___x_389_);
                        if v___x_395_ == 0 {
                            leanh::lean_dec(v___x_392_);
                            leanh::lean_dec_ref(v_id_373_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_392_);
                            v___x_396_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_396_, 0, v_id_373_);
                            leanh::lean_ctor_set(v___x_396_, 1, v___x_392_);
                            leanh::lean_ctor_set(v___x_396_, 2, v___x_389_);
                            v___y_375_ = v___x_396_;
                            v_startInclusive_376_ = v___x_392_;
                            v_endExclusive_377_ = v___x_389_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v___y_398_ == 0 {
                    leanh::lean_dec_ref(v_id_373_);
                    return v___y_398_;
                } else {
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_401_ = 97;
                v___x_402_ = lean_uint32_dec_le(v___x_401_, v___y_400_);
                if v___x_402_ == 0 {
                    v___y_398_ = v___x_402_;
                    state = 4;
                    continue;
                } else {
                    v___x_403_ = 122;
                    v___x_404_ = lean_uint32_dec_le(v___y_400_, v___x_403_);
                    v___y_398_ = v___x_404_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_407_ = 65;
                v___x_408_ = lean_uint32_dec_le(v___x_407_, v___y_406_);
                if v___x_408_ == 0 {
                    v___y_400_ = v___y_406_;
                    state = 5;
                    continue;
                } else {
                    v___x_409_ = 90;
                    v___x_410_ = lean_uint32_dec_le(v___y_406_, v___x_409_);
                    if v___x_410_ == 0 {
                        v___y_400_ = v___y_406_;
                        state = 5;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId___boxed(
    mut v_id_418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_419_: u8 = 0;
    let mut v_r_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_419_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_id_418_);
    v_r_420_ = leanh::lean_box((v_res_419_) as usize);
    return v_r_420_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(
    mut v_x_421_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_pre_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: u8 = 0;
    let mut v_str_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v___x_428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_421_) == 1 {
                    v_pre_422_ = leanh::lean_ctor_get(v_x_421_, 0);
                    if leanh::lean_obj_tag(v_pre_422_) == 0 {
                        v_str_423_ = leanh::lean_ctor_get(v_x_421_, 1);
                        leanh::lean_inc_ref(v_str_423_);
                        leanh::lean_dec_ref_known(v_x_421_, 2);
                        v___x_424_ =
                            l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_423_);
                        return v___x_424_;
                    } else {
                        leanh::lean_inc(v_pre_422_);
                        v_str_425_ = leanh::lean_ctor_get(v_x_421_, 1);
                        leanh::lean_inc_ref(v_str_425_);
                        leanh::lean_dec_ref_known(v_x_421_, 2);
                        v___x_426_ =
                            l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppId(v_str_425_);
                        if v___x_426_ == 0 {
                            leanh::lean_dec(v_pre_422_);
                            return v___x_426_;
                        } else {
                            v_x_421_ = v_pre_422_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_421_);
                    v___x_428_ = 0;
                    return v___x_428_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName___boxed(
    mut v_x_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_x_429_);
    v_r_431_ = leanh::lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_432_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_434_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_434_, 0, v___x_433_);
    return v___x_434_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_436_ = leanh::lean_unsigned_to_nat(0);
    v___x_437_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_437_, 0, v___x_436_);
    leanh::lean_ctor_set(v___x_437_, 1, v___x_436_);
    leanh::lean_ctor_set(v___x_437_, 2, v___x_436_);
    leanh::lean_ctor_set(v___x_437_, 3, v___x_436_);
    leanh::lean_ctor_set(v___x_437_, 4, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 5, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 6, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 7, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 8, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 9, v___x_435_);
    return v___x_437_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = leanh::lean_unsigned_to_nat(32);
    v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
    v___x_440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_440_, 0, v___x_439_);
    return v___x_440_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_441_: usize = 0;
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = 5usize;
    v___x_442_ = leanh::lean_unsigned_to_nat(0);
    v___x_443_ = leanh::lean_unsigned_to_nat(32);
    v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
    v___x_445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_446_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_446_, 0, v___x_445_);
    leanh::lean_ctor_set(v___x_446_, 1, v___x_444_);
    leanh::lean_ctor_set(v___x_446_, 2, v___x_442_);
    leanh::lean_ctor_set(v___x_446_, 3, v___x_442_);
    leanh::lean_ctor_set_usize(v___x_446_, 4, v___x_441_);
    return v___x_446_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_447_ = leanh::lean_box(1);
    v___x_448_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_450_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_450_, 0, v___x_449_);
    leanh::lean_ctor_set(v___x_450_, 1, v___x_448_);
    leanh::lean_ctor_set(v___x_450_, 2, v___x_447_);
    return v___x_450_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_451_: *mut leanh::LeanObject,
    mut v___y_452_: *mut leanh::LeanObject,
    mut v___y_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = lean_st_ref_get(v___y_453_);
    v_env_456_ = leanh::lean_ctor_get(v___x_455_, 0);
    leanh::lean_inc_ref(v_env_456_);
    leanh::lean_dec(v___x_455_);
    v_options_457_ = leanh::lean_ctor_get(v___y_452_, 2);
    v___x_458_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_457_);
    v___x_460_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_460_, 0, v_env_456_);
    leanh::lean_ctor_set(v___x_460_, 1, v___x_458_);
    leanh::lean_ctor_set(v___x_460_, 2, v___x_459_);
    leanh::lean_ctor_set(v___x_460_, 3, v_options_457_);
    v___x_461_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_461_, 0, v___x_460_);
    leanh::lean_ctor_set(v___x_461_, 1, v_msgData_451_);
    v___x_462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_462_, 0, v___x_461_);
    return v___x_462_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0(v_msgData_463_, v___y_464_, v___y_465_);
    leanh::lean_dec(v___y_465_);
    leanh::lean_dec_ref(v___y_464_);
    return v_res_467_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
    mut v___y_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_472_ = leanh::lean_ctor_get(v___y_469_, 5);
                v___x_473_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0_spec__0(v_msg_468_, v___y_469_, v___y_470_);
                v_a_474_ = leanh::lean_ctor_get(v___x_473_, 0);
                v_isSharedCheck_482_ = (!leanh::lean_is_exclusive(v___x_473_)) as u8;
                if v_isSharedCheck_482_ == 0 {
                    v___x_476_ = v___x_473_;
                    v_isShared_477_ = v_isSharedCheck_482_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_474_);
                    leanh::lean_dec(v___x_473_);
                    v___x_476_ = leanh::lean_box(0);
                    v_isShared_477_ = v_isSharedCheck_482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_472_);
                v___x_478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_478_, 0, v_ref_472_);
                leanh::lean_ctor_set(v___x_478_, 1, v_a_474_);
                if v_isShared_477_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_476_, 1);
                    leanh::lean_ctor_set(v___x_476_, 0, v___x_478_);
                    v___x_480_ = v___x_476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
                    v___x_480_ = v_reuseFailAlloc_481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_483_: *mut leanh::LeanObject,
    mut v___y_484_: *mut leanh::LeanObject,
    mut v___y_485_: *mut leanh::LeanObject,
    mut v___y_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0___redArg(v_msg_483_, v___y_484_, v___y_485_);
    leanh::lean_dec(v___y_485_);
    leanh::lean_dec_ref(v___y_484_);
    return v_res_487_;
}
pub unsafe fn _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_;
    v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
    return v___x_490_;
}
pub unsafe fn _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_;
    v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
    return v___x_493_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_(
    mut v_x_494_: *mut leanh::LeanObject,
    mut v_stx_495_: *mut leanh::LeanObject,
    mut v___y_496_: *mut leanh::LeanObject,
    mut v___y_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_511_: u8 = 0;
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_515_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_499_ = l_Lean_Attribute_Builtin_getId(v_stx_495_, v___y_496_, v___y_497_);
                if leanh::lean_obj_tag(v___x_499_) == 0 {
                    v_a_500_ = leanh::lean_ctor_get(v___x_499_, 0);
                    leanh::lean_inc_n(v_a_500_, 2);
                    v___x_501_ =
                        l___private_Lean_Compiler_ExportAttr_0__Lean_isValidCppName(v_a_500_);
                    if v___x_501_ == 0 {
                        leanh::lean_dec_ref_known(v___x_499_, 1);
                        v___x_502_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_);
                        v___x_503_ = l_Lean_MessageData_ofName(v_a_500_);
                        v___x_504_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_504_, 0, v___x_502_);
                        leanh::lean_ctor_set(v___x_504_, 1, v___x_503_);
                        v___x_505_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_);
                        v___x_506_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_506_, 0, v___x_504_);
                        leanh::lean_ctor_set(v___x_506_, 1, v___x_505_);
                        v___x_507_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0___redArg(v___x_506_, v___y_496_, v___y_497_);
                        v_a_508_ = leanh::lean_ctor_get(v___x_507_, 0);
                        v_isSharedCheck_515_ = (!leanh::lean_is_exclusive(v___x_507_)) as u8;
                        if v_isSharedCheck_515_ == 0 {
                            v___x_510_ = v___x_507_;
                            v_isShared_511_ = v_isSharedCheck_515_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_508_);
                            leanh::lean_dec(v___x_507_);
                            v___x_510_ = leanh::lean_box(0);
                            v_isShared_511_ = v_isSharedCheck_515_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_500_);
                        return v___x_499_;
                    }
                } else {
                    return v___x_499_;
                }
            }
            1 => {
                if v_isShared_511_ == 0 {
                    v___x_513_ = v___x_510_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_514_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
                    v___x_513_ = v_reuseFailAlloc_514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed(
    mut v_x_516_: *mut leanh::LeanObject,
    mut v_stx_517_: *mut leanh::LeanObject,
    mut v___y_518_: *mut leanh::LeanObject,
    mut v___y_519_: *mut leanh::LeanObject,
    mut v___y_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_521_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_(v_x_516_, v_stx_517_, v___y_518_, v___y_519_);
    leanh::lean_dec(v___y_519_);
    leanh::lean_dec_ref(v___y_518_);
    leanh::lean_dec(v_x_516_);
    return v_res_521_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_(
    mut v_x_522_: *mut leanh::LeanObject,
    mut v_x_523_: *mut leanh::LeanObject,
    mut v_x_524_: *mut leanh::LeanObject,
    mut v___y_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = leanh::lean_box(0);
    v___x_528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_528_, 0, v___x_527_);
    return v___x_528_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed(
    mut v_x_529_: *mut leanh::LeanObject,
    mut v_x_530_: *mut leanh::LeanObject,
    mut v_x_531_: *mut leanh::LeanObject,
    mut v___y_532_: *mut leanh::LeanObject,
    mut v___y_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_534_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_(v_x_529_, v_x_530_, v_x_531_, v___y_532_);
    leanh::lean_dec(v___y_532_);
    leanh::lean_dec_ref(v_x_531_);
    leanh::lean_dec(v_x_530_);
    leanh::lean_dec(v_x_529_);
    return v_res_534_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_(
    mut v___x_535_: u8,
    mut v_env_536_: *mut leanh::LeanObject,
    mut v_n_537_: *mut leanh::LeanObject,
    mut v_x_538_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_539_: u8 = 0;
    v___x_539_ = l_Lean_Environment_contains(v_env_536_, v_n_537_, v___x_535_);
    return v___x_539_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed(
    mut v___x_540_: *mut leanh::LeanObject,
    mut v_env_541_: *mut leanh::LeanObject,
    mut v_n_542_: *mut leanh::LeanObject,
    mut v_x_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1526__boxed_544_: u8 = 0;
    let mut v_res_545_: u8 = 0;
    let mut v_r_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1526__boxed_544_ = (leanh::lean_unbox(v___x_540_) as u8);
    v_res_545_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_(v___x_1526__boxed_544_, v_env_541_, v_n_542_, v_x_543_);
    leanh::lean_dec(v_x_543_);
    v_r_546_ = leanh::lean_box((v_res_545_) as usize);
    return v_r_546_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_;
    v___x_574_ = l_Lean_registerParametricAttribute___redArg(v___x_573_);
    return v___x_574_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2____boxed(
    mut v_a_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_576_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_();
    return v_res_576_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_577_: *mut leanh::LeanObject,
    mut v_msg_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0___redArg(v_msg_578_, v___y_579_, v___y_580_);
    return v___x_582_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_583_: *mut leanh::LeanObject,
    mut v_msg_584_: *mut leanh::LeanObject,
    mut v___y_585_: *mut leanh::LeanObject,
    mut v___y_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_throwError___at___00__private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2__spec__0(v_00_u03b1_583_, v_msg_584_, v___y_585_, v___y_586_);
    leanh::lean_dec(v___y_586_);
    leanh::lean_dec_ref(v___y_585_);
    return v_res_588_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1()
-> *mut leanh::LeanObject {
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_591_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_;
    v___x_592_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___closed__0;
    v___x_593_ = l_Lean_addBuiltinDocString(v___x_591_, v___x_592_);
    return v___x_593_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1___boxed(
    mut v_a_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_595_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
    return v_res_595_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_;
    v___x_623_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___closed__6;
    v___x_624_ = l_Lean_addBuiltinDeclarationRanges(v___x_622_, v___x_623_);
    return v___x_624_;
}
pub unsafe fn l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3___boxed(
    mut v_a_625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
    return v_res_626_;
}
pub unsafe fn lean_get_export_name_for(
    mut v_env_627_: *mut leanh::LeanObject,
    mut v_n_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = leanh::lean_box(0);
    v___x_630_ = l_Lean_exportAttr;
    v___x_631_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_629_, v___x_630_, v_env_627_, v_n_628_,
    );
    return v___x_631_;
}
pub unsafe fn l_Lean_isExport(
    mut v_env_635_: *mut leanh::LeanObject,
    mut v_n_636_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_n_636_);
    v___x_637_ = lean_get_export_name_for(v_env_635_, v_n_636_);
    if leanh::lean_obj_tag(v___x_637_) == 0 {
        let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_639_: u8 = 0;
        v___x_638_ = l_Lean_isExport___closed__1;
        v___x_639_ = lean_name_eq(v_n_636_, v___x_638_);
        leanh::lean_dec(v_n_636_);
        return v___x_639_;
    } else {
        let mut v___x_640_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_637_, 1);
        leanh::lean_dec(v_n_636_);
        v___x_640_ = 1;
        return v___x_640_;
    }
}
pub unsafe fn l_Lean_isExport___boxed(
    mut v_env_641_: *mut leanh::LeanObject,
    mut v_n_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lean_isExport(v_env_641_, v_n_642_);
    v_r_644_ = leanh::lean_box((v_res_643_) as usize);
    return v_r_644_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_ExportAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_ExportAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExportAttr_163978030____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_exportAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_exportAttr);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_ExportAttr_0__Lean_exportAttr___regBuiltin_Lean_exportAttr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_ExportAttr(
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
pub unsafe fn initialize_Lean_Compiler_ExportAttr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_ExportAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_ExportAttr(builtin);
}