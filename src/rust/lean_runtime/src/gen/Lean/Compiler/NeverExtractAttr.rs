// Lean compiler output
// Module: Lean.Compiler.NeverExtractAttr
// Imports: Lean.Attributes
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute,
    runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isInternal};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 101, 118, 101, 114, 95, 101, 120, 116, 114, 97, 99, 116, 0]};
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2703892099028076162 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<236> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 236, m_capacity: 236, m_length: 235, m_data: [105, 110, 115, 116, 114, 117, 99, 116, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 116, 104, 97, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 101, 120, 116, 114, 97, 99, 116, 101, 100, 32, 119, 104, 101, 110, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 99, 108, 111, 115, 101, 100, 32, 116, 101, 114, 109, 115, 44, 32, 110, 111, 114, 32, 99, 111, 109, 109, 111, 110, 32, 115, 117, 98, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 112, 101, 114, 102, 111, 114, 109, 101, 100, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 104, 97, 118, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 101, 102, 102, 101, 99, 116, 115, 46, 0]};
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 101, 118, 101, 114, 69, 120, 116, 114, 97, 99, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3821166207137907747 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<512> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 512, m_capacity: 512, m_length: 511, m_data: [73, 110, 115, 116, 114, 117, 99, 116, 115, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 116, 104, 97, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 10, 101, 120, 116, 114, 97, 99, 116, 101, 100, 32, 119, 104, 101, 110, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 99, 108, 111, 115, 101, 100, 32, 116, 101, 114, 109, 115, 44, 32, 97, 110, 100, 32, 116, 104, 97, 116, 32, 99, 111, 109, 109, 111, 110, 32, 115, 117, 98, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 101, 108, 105, 109, 105, 110, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 10, 112, 101, 114, 102, 111, 114, 109, 101, 100, 46, 10, 10, 79, 114, 100, 105, 110, 97, 114, 105, 108, 121, 44, 32, 116, 104, 101, 32, 76, 101, 97, 110, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 115, 32, 99, 108, 111, 115, 101, 100, 32, 116, 101, 114, 109, 115, 32, 40, 119, 105, 116, 104, 111, 117, 116, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 41, 32, 97, 110, 100, 32, 101, 120, 116, 114, 97, 99, 116, 115, 32, 116, 104, 101, 109, 10, 116, 111, 32, 116, 111, 112, 45, 108, 101, 118, 101, 108, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 46, 32, 84, 104, 105, 115, 32, 111, 112, 116, 105, 109, 105, 122, 97, 116, 105, 111, 110, 32, 99, 97, 110, 32, 112, 114, 101, 118, 101, 110, 116, 32, 117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 32, 114, 101, 99, 111, 109, 112, 117, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 118, 97, 108, 117, 101, 115, 46, 10, 10, 80, 114, 101, 118, 101, 110, 116, 105, 110, 103, 32, 116, 104, 101, 32, 101, 120, 116, 114, 97, 99, 116, 105, 111, 110, 32, 111, 102, 32, 99, 108, 111, 115, 101, 100, 32, 116, 101, 114, 109, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 104, 97, 118, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 101, 102, 102, 101, 99, 116, 115, 10, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 114, 101, 112, 101, 97, 116, 101, 100, 46, 10, 0]};
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 275 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 275 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(
    mut v_x_88_: *mut crate::leanh::LeanObject,
    mut v___y_89_: *mut crate::leanh::LeanObject,
    mut v___y_90_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_92_ = crate::leanh::lean_box(0);
    v___x_93_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_93_, 0, v___x_92_);
    return v___x_93_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(
    mut v_x_94_: *mut crate::leanh::LeanObject,
    mut v___y_95_: *mut crate::leanh::LeanObject,
    mut v___y_96_: *mut crate::leanh::LeanObject,
    mut v___y_97_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_98_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_(v_x_94_, v___y_95_, v___y_96_);
    crate::leanh::lean_dec(v___y_96_);
    crate::leanh::lean_dec_ref(v___y_95_);
    crate::leanh::lean_dec(v_x_94_);
    return v_res_98_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: u8 = 0;
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_110_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_;
    v___x_111_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_;
    v___x_112_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_;
    v___x_113_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_;
    v___x_114_ = 0;
    v___x_115_ = crate::leanh::lean_box(2);
    v___x_116_ = l_Lean_registerTagAttribute(
        v___x_111_, v___x_112_, v___f_110_, v___x_113_, v___x_114_, v___x_115_,
    );
    return v___x_116_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2____boxed(
    mut v_a_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
    return v_res_118_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_121_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_;
    v___x_122_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___closed__0;
    v___x_123_ = l_Lean_addBuiltinDocString(v___x_121_, v___x_122_);
    return v___x_123_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1___boxed(
    mut v_a_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_125_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
    return v_res_125_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_;
    v___x_153_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___closed__6;
    v___x_154_ = l_Lean_addBuiltinDeclarationRanges(v___x_152_, v___x_153_);
    return v___x_154_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3___boxed(
    mut v_a_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_156_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
    return v_res_156_;
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(
    mut v_env_157_: *mut crate::leanh::LeanObject,
    mut v_n_158_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: u8 = 0;
    let mut v___x_161_: u8 = 0;
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_159_ = l_Lean_neverExtractAttr;
                crate::leanh::lean_inc(v_n_158_);
                crate::leanh::lean_inc_ref(v_env_157_);
                v___x_160_ = l_Lean_TagAttribute_hasTag(v___x_159_, v_env_157_, v_n_158_);
                if v___x_160_ == 0 {
                    v___x_161_ = l_Lean_Name_isInternal(v_n_158_);
                    if v___x_161_ == 0 {
                        crate::leanh::lean_dec(v_n_158_);
                        crate::leanh::lean_dec_ref(v_env_157_);
                        return v___x_161_;
                    } else {
                        v___x_162_ = l_Lean_Name_getPrefix(v_n_158_);
                        crate::leanh::lean_dec(v_n_158_);
                        v_n_158_ = v___x_162_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_158_);
                    crate::leanh::lean_dec_ref(v_env_157_);
                    return v___x_160_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit___boxed(
    mut v_env_164_: *mut crate::leanh::LeanObject,
    mut v_n_165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_166_: u8 = 0;
    let mut v_r_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_166_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(
        v_env_164_, v_n_165_,
    );
    v_r_167_ = crate::leanh::lean_box((v_res_166_) as usize);
    return v_r_167_;
}
pub unsafe fn l_Lean_hasNeverExtractAttribute(
    mut v_env_168_: *mut crate::leanh::LeanObject,
    mut v_n_169_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_170_: u8 = 0;
    v___x_170_ = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_hasNeverExtractAttribute_visit(
        v_env_168_, v_n_169_,
    );
    return v___x_170_;
}
pub unsafe fn l_Lean_hasNeverExtractAttribute___boxed(
    mut v_env_171_: *mut crate::leanh::LeanObject,
    mut v_n_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_173_: u8 = 0;
    let mut v_r_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_173_ = l_Lean_hasNeverExtractAttribute(v_env_171_, v_n_172_);
    v_r_174_ = crate::leanh::lean_box((v_res_173_) as usize);
    return v_r_174_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_NeverExtractAttr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_initFn_00___x40_Lean_Compiler_NeverExtractAttr_1636298006____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_neverExtractAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_neverExtractAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_NeverExtractAttr_0__Lean_neverExtractAttr___regBuiltin_Lean_neverExtractAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_NeverExtractAttr(
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
pub unsafe fn initialize_Lean_Compiler_NeverExtractAttr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_NeverExtractAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_NeverExtractAttr(builtin);
}
