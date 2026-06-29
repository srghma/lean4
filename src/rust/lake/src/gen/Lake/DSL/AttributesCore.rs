// Lean compiler output
// Module: Lake.DSL.AttributesCore
// Imports: Lake.Util.OrderedTagAttribute
use crate::r#gen::Lake::Util::OrderedTagAttribute::{
    initialize_Lake_Util_OrderedTagAttribute, l_Lake_OrderedTagAttribute_hasTag,
    l_Lake_registerOrderedTagAttribute, runtime_initialize_Lake_Util_OrderedTagAttribute,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 97, 99, 107, 97, 103, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6671755061125946191 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 99, 107, 97, 103, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,659528549093005558 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_packageAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 99, 107, 97, 103, 101, 95, 100, 101, 112, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4808916106510604781 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 97, 99, 107, 97, 103, 101, 68, 101, 112, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2574662391088497709 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_packageDepAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 111, 115, 116, 95, 117, 112, 100, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,985716791886485019 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 112, 111, 115, 116, 45, 117, 112, 100, 97, 116, 101, 32, 104, 111, 111, 107, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12436946493679816533 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_postUpdateAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,887671011676595348 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 99, 114, 105, 112, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14767982047059385626 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_scriptAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 100, 101, 102, 97, 117, 108, 116, 95, 115, 99, 114, 105, 112, 116, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 96, 115, 99, 114, 105, 112, 116, 96, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 102, 97, 117, 108, 116, 95, 115, 99, 114, 105, 112, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16430358650169544679 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 32, 97, 115, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 102, 97, 117, 108, 116, 83, 99, 114, 105, 112, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,758561379943963750 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_defaultScriptAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12295998048739818339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 76, 101, 97, 110, 32, 108, 105, 98, 114, 97, 114, 121, 32, 116, 97, 114, 103, 101, 116, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 97, 110, 76, 105, 98, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7818855776703404064 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_leanLibAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 101, 120, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10587356296225942211 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 76, 101, 97, 110, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 116, 97, 114, 103, 101, 116, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 97, 110, 69, 120, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11424057956103599804 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_leanExeAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11562366611225967008 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 101, 120, 116, 101, 114, 110, 97, 108, 32, 108, 105, 98, 114, 97, 114, 121, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 116, 101, 114, 110, 76, 105, 98, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7509421779037782117 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_externLibAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4067501922346325234 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 105, 110, 112, 117, 116, 32, 102, 105, 108, 101, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 112, 117, 116, 70, 105, 108, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17885622076320419789 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_inputFileAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9710019104504222840 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 105, 110, 112, 117, 116, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 112, 117, 116, 68, 105, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12085934795154313082 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_inputDirAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6124717609876119291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 114, 103, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9199123000070154982 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_targetAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<87> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 87, m_capacity: 87, m_length: 86, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 100, 101, 102, 97, 117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 116, 97, 114, 103, 101, 116, 32, 40, 101, 46, 103, 46, 44, 32, 96, 108, 101, 97, 110, 95, 108, 105, 98, 96, 44, 32, 96, 108, 101, 97, 110, 95, 101, 120, 101, 96, 41, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 102, 97, 117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12969074616217864974 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 116, 97, 114, 103, 101, 116, 32, 97, 115, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 101, 102, 97, 117, 108, 116, 84, 97, 114, 103, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8325663718235124360 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_defaultTargetAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<82> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 96, 115, 99, 114, 105, 112, 116, 96, 44, 32, 96, 108, 101, 97, 110, 95, 101, 120, 101, 96, 44, 32, 111, 114, 32, 96, 108, 101, 97, 110, 95, 108, 105, 98, 96, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2705511379774931411 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 44, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 44, 32, 111, 114, 32, 108, 105, 98, 114, 97, 114, 121, 32, 97, 115, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 116, 101, 115, 116, 32, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 115, 116, 68, 114, 105, 118, 101, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1466235757312191377 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_testDriverAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 108, 105, 110, 116, 95, 100, 114, 105, 118, 101, 114, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 110, 32, 97, 32, 96, 115, 99, 114, 105, 112, 116, 96, 32, 111, 114, 32, 96, 108, 101, 97, 110, 95, 101, 120, 101, 96, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 105, 110, 116, 95, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11055114253656833314 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [109, 97, 114, 107, 32, 97, 32, 76, 97, 107, 101, 32, 115, 99, 114, 105, 112, 116, 32, 111, 114, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 97, 115, 32, 112, 97, 99, 107, 97, 103, 101, 39, 115, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 105, 110, 116, 68, 114, 105, 118, 101, 114, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12055850808226400418 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_lintDriverAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 111, 100, 117, 108, 101, 95, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9448625530981317401 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 109, 111, 100, 117, 108, 101, 32, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [109, 111, 100, 117, 108, 101, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11171157541301760440 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_moduleFacetAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 99, 107, 97, 103, 101, 95, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9378971393347028642 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18143559972510357022 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_packageFacetAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 105, 98, 114, 97, 114, 121, 95, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17310535023809783662 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [109, 97, 114, 107, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 97, 107, 101, 32, 108, 105, 98, 114, 97, 114, 121, 32, 102, 97, 99, 101, 116, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3952046105223012164 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_libraryFacetAttr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(
    mut v_x_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = crate::leanh::lean_box(0);
    v___x_607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_607_, 0, v___x_606_);
    return v___x_607_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(
    mut v_x_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_612_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_(v_x_608_, v___y_609_, v___y_610_);
    crate::leanh::lean_dec(v___y_610_);
    crate::leanh::lean_dec_ref(v___y_609_);
    crate::leanh::lean_dec(v_x_608_);
    return v_res_612_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_624_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_625_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_626_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_627_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_628_ = l_Lake_registerOrderedTagAttribute(v___x_625_, v___x_626_, v___f_624_, v___x_627_);
    return v___x_628_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2____boxed(
    mut v_a_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
    return v_res_630_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_640_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_641_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_;
    v___x_642_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_;
    v___x_643_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_;
    v___x_644_ = l_Lake_registerOrderedTagAttribute(v___x_641_, v___x_642_, v___f_640_, v___x_643_);
    return v___x_644_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2____boxed(
    mut v_a_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
    return v_res_646_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_656_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_657_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_;
    v___x_658_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_;
    v___x_659_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_;
    v___x_660_ = l_Lake_registerOrderedTagAttribute(v___x_657_, v___x_658_, v___f_656_, v___x_659_);
    return v___x_660_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2____boxed(
    mut v_a_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_662_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
    return v_res_662_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_672_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_673_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_;
    v___x_674_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_;
    v___x_675_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_;
    v___x_676_ = l_Lake_registerOrderedTagAttribute(v___x_673_, v___x_674_, v___f_672_, v___x_675_);
    return v___x_676_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2____boxed(
    mut v_a_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
    return v_res_678_;
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(
    mut v_a_679_: *mut crate::leanh::LeanObject,
    mut v_f_680_: *mut crate::leanh::LeanObject,
    mut v___y_681_: *mut crate::leanh::LeanObject,
    mut v___y_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_a_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_697_: u8 = 0;
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_682_);
                crate::leanh::lean_inc_ref(v___y_681_);
                v___x_684_ = crate::leanh::lean_apply_3(
                    v_a_679_,
                    v___y_681_,
                    v___y_682_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_684_) == 0 {
                    v_a_685_ = crate::leanh::lean_ctor_get(v___x_684_, 0);
                    v_isSharedCheck_693_ = (!crate::leanh::lean_is_exclusive(v___x_684_)) as u8;
                    if v_isSharedCheck_693_ == 0 {
                        v___x_687_ = v___x_684_;
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_685_);
                        crate::leanh::lean_dec(v___x_684_);
                        v___x_687_ = crate::leanh::lean_box(0);
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_680_);
                    v_a_694_ = crate::leanh::lean_ctor_get(v___x_684_, 0);
                    v_isSharedCheck_701_ = (!crate::leanh::lean_is_exclusive(v___x_684_)) as u8;
                    if v_isSharedCheck_701_ == 0 {
                        v___x_696_ = v___x_684_;
                        v_isShared_697_ = v_isSharedCheck_701_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_694_);
                        crate::leanh::lean_dec(v___x_684_);
                        v___x_696_ = crate::leanh::lean_box(0);
                        v_isShared_697_ = v_isSharedCheck_701_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_689_ = crate::leanh::lean_apply_1(v_f_680_, v_a_685_);
                if v_isShared_688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_687_, 0, v___x_689_);
                    v___x_691_ = v___x_687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
                    v___x_691_ = v_reuseFailAlloc_692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_691_;
            }
            3 => {
                if v_isShared_697_ == 0 {
                    v___x_699_ = v___x_696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
                    v___x_699_ = v_reuseFailAlloc_700_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_f_703_: *mut crate::leanh::LeanObject,
    mut v___y_704_: *mut crate::leanh::LeanObject,
    mut v___y_705_: *mut crate::leanh::LeanObject,
    mut v___y_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_707_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v_a_702_, v_f_703_, v___y_704_, v___y_705_);
    crate::leanh::lean_dec(v___y_705_);
    crate::leanh::lean_dec_ref(v___y_704_);
    return v_res_707_;
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_708_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_709_: *mut crate::leanh::LeanObject,
    mut v_a_710_: *mut crate::leanh::LeanObject,
    mut v_f_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
    mut v___y_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_715_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v_a_710_, v_f_711_, v___y_712_, v___y_713_);
    return v___x_715_;
}
pub unsafe fn l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_716_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
    mut v_f_719_: *mut crate::leanh::LeanObject,
    mut v___y_720_: *mut crate::leanh::LeanObject,
    mut v___y_721_: *mut crate::leanh::LeanObject,
    mut v___y_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0(v_00_u03b1_716_, v_00_u03b2_717_, v_a_718_, v_f_719_, v___y_720_, v___y_721_);
    crate::leanh::lean_dec(v___y_721_);
    crate::leanh::lean_dec_ref(v___y_720_);
    return v_res_723_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(
    mut v___y_724_: *mut crate::leanh::LeanObject,
    mut v___y_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = lean_st_ref_get(v___y_725_);
    v_env_728_ = crate::leanh::lean_ctor_get(v___x_727_, 0);
    crate::leanh::lean_inc_ref(v_env_728_);
    crate::leanh::lean_dec(v___x_727_);
    v___x_729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_729_, 0, v_env_728_);
    return v___x_729_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v___y_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___y_730_, v___y_731_);
    crate::leanh::lean_dec(v___y_731_);
    crate::leanh::lean_dec_ref(v___y_730_);
    return v_res_733_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(
    mut v_name_734_: *mut crate::leanh::LeanObject,
    mut v_x_735_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    v___x_736_ = l_Lake_scriptAttr;
    v___x_737_ = l_Lake_OrderedTagAttribute_hasTag(v___x_736_, v_x_735_, v_name_734_);
    return v___x_737_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v_name_738_: *mut crate::leanh::LeanObject,
    mut v_x_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_740_: u8 = 0;
    let mut v_r_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v_name_738_, v_x_739_);
    crate::leanh::lean_dec(v_name_738_);
    v_r_741_ = crate::leanh::lean_box((v_res_740_) as usize);
    return v_r_741_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_742_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_742_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__0);
    v___x_744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_744_, 0, v___x_743_);
    return v___x_744_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
    v___x_746_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_747_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_747_, 0, v___x_746_);
    crate::leanh::lean_ctor_set(v___x_747_, 1, v___x_746_);
    crate::leanh::lean_ctor_set(v___x_747_, 2, v___x_746_);
    crate::leanh::lean_ctor_set(v___x_747_, 3, v___x_746_);
    crate::leanh::lean_ctor_set(v___x_747_, 4, v___x_745_);
    crate::leanh::lean_ctor_set(v___x_747_, 5, v___x_745_);
    crate::leanh::lean_ctor_set(v___x_747_, 6, v___x_745_);
    crate::leanh::lean_ctor_set(v___x_747_, 7, v___x_745_);
    crate::leanh::lean_ctor_set(v___x_747_, 8, v___x_745_);
    crate::leanh::lean_ctor_set(v___x_747_, 9, v___x_745_);
    return v___x_747_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_748_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_749_ = lean_mk_empty_array_with_capacity(v___x_748_);
    v___x_750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_750_, 0, v___x_749_);
    return v___x_750_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_751_: usize = 0;
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_751_ = 5usize;
    v___x_752_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_753_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
    v___x_755_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__3);
    v___x_756_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_756_, 0, v___x_755_);
    crate::leanh::lean_ctor_set(v___x_756_, 1, v___x_754_);
    crate::leanh::lean_ctor_set(v___x_756_, 2, v___x_752_);
    crate::leanh::lean_ctor_set(v___x_756_, 3, v___x_752_);
    crate::leanh::lean_ctor_set_usize(v___x_756_, 4, v___x_751_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = crate::leanh::lean_box(1);
    v___x_758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__4);
    v___x_759_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__1);
    v___x_760_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_760_, 0, v___x_759_);
    crate::leanh::lean_ctor_set(v___x_760_, 1, v___x_758_);
    crate::leanh::lean_ctor_set(v___x_760_, 2, v___x_757_);
    return v___x_760_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(
    mut v_msgData_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = lean_st_ref_get(v___y_763_);
    v_env_766_ = crate::leanh::lean_ctor_get(v___x_765_, 0);
    crate::leanh::lean_inc_ref(v_env_766_);
    crate::leanh::lean_dec(v___x_765_);
    v_options_767_ = crate::leanh::lean_ctor_get(v___y_762_, 2);
    v___x_768_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__2);
    v___x_769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___closed__5);
    crate::leanh::lean_inc_ref(v_options_767_);
    v___x_770_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_770_, 0, v_env_766_);
    crate::leanh::lean_ctor_set(v___x_770_, 1, v___x_768_);
    crate::leanh::lean_ctor_set(v___x_770_, 2, v___x_769_);
    crate::leanh::lean_ctor_set(v___x_770_, 3, v_options_767_);
    v___x_771_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_771_, 0, v___x_770_);
    crate::leanh::lean_ctor_set(v___x_771_, 1, v_msgData_761_);
    v___x_772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_msgData_773_: *mut crate::leanh::LeanObject,
    mut v___y_774_: *mut crate::leanh::LeanObject,
    mut v___y_775_: *mut crate::leanh::LeanObject,
    mut v___y_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msgData_773_, v___y_774_, v___y_775_);
    crate::leanh::lean_dec(v___y_775_);
    crate::leanh::lean_dec_ref(v___y_774_);
    return v_res_777_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(
    mut v_msg_778_: *mut crate::leanh::LeanObject,
    mut v___y_779_: *mut crate::leanh::LeanObject,
    mut v___y_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_782_ = crate::leanh::lean_ctor_get(v___y_779_, 5);
                v___x_783_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1_spec__1(v_msg_778_, v___y_779_, v___y_780_);
                v_a_784_ = crate::leanh::lean_ctor_get(v___x_783_, 0);
                v_isSharedCheck_792_ = (!crate::leanh::lean_is_exclusive(v___x_783_)) as u8;
                if v_isSharedCheck_792_ == 0 {
                    v___x_786_ = v___x_783_;
                    v_isShared_787_ = v_isSharedCheck_792_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_784_);
                    crate::leanh::lean_dec(v___x_783_);
                    v___x_786_ = crate::leanh::lean_box(0);
                    v_isShared_787_ = v_isSharedCheck_792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_782_);
                v___x_788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_788_, 0, v_ref_782_);
                crate::leanh::lean_ctor_set(v___x_788_, 1, v_a_784_);
                if v_isShared_787_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_786_, 1);
                    crate::leanh::lean_ctor_set(v___x_786_, 0, v___x_788_);
                    v___x_790_ = v___x_786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
                    v___x_790_ = v_reuseFailAlloc_791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_msg_793_: *mut crate::leanh::LeanObject,
    mut v___y_794_: *mut crate::leanh::LeanObject,
    mut v___y_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_793_, v___y_794_, v___y_795_);
    crate::leanh::lean_dec(v___y_795_);
    crate::leanh::lean_dec_ref(v___y_794_);
    return v_res_797_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__0_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
    return v___x_800_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(
    mut v___f_801_: *mut crate::leanh::LeanObject,
    mut v_name_802_: *mut crate::leanh::LeanObject,
    mut v___y_803_: *mut crate::leanh::LeanObject,
    mut v___y_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_811_: u8 = 0;
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_a_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_806_ = crate::leanh::lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_806_, 0, v_name_802_);
                v___x_807_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_801_, v___f_806_, v___y_803_, v___y_804_);
                if crate::leanh::lean_obj_tag(v___x_807_) == 0 {
                    v_a_808_ = crate::leanh::lean_ctor_get(v___x_807_, 0);
                    v_isSharedCheck_819_ = (!crate::leanh::lean_is_exclusive(v___x_807_)) as u8;
                    if v_isSharedCheck_819_ == 0 {
                        v___x_810_ = v___x_807_;
                        v_isShared_811_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_808_);
                        crate::leanh::lean_dec(v___x_807_);
                        v___x_810_ = crate::leanh::lean_box(0);
                        v_isShared_811_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_820_ = crate::leanh::lean_ctor_get(v___x_807_, 0);
                    v_isSharedCheck_827_ = (!crate::leanh::lean_is_exclusive(v___x_807_)) as u8;
                    if v_isSharedCheck_827_ == 0 {
                        v___x_822_ = v___x_807_;
                        v_isShared_823_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_820_);
                        crate::leanh::lean_dec(v___x_807_);
                        v___x_822_ = crate::leanh::lean_box(0);
                        v_isShared_823_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_812_ = (crate::leanh::lean_unbox(v_a_808_) as u8);
                crate::leanh::lean_dec(v_a_808_);
                if v___x_812_ == 0 {
                    crate::leanh::lean_del_object(v___x_810_);
                    v___x_813_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_);
                    v___x_814_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_813_, v___y_803_, v___y_804_);
                    return v___x_814_;
                } else {
                    v___x_815_ = crate::leanh::lean_box(0);
                    if v_isShared_811_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_810_, 0, v___x_815_);
                        v___x_817_ = v___x_810_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
                        v___x_817_ = v_reuseFailAlloc_818_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_817_;
            }
            3 => {
                if v_isShared_823_ == 0 {
                    v___x_825_ = v___x_822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
                    v___x_825_ = v_reuseFailAlloc_826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v___f_828_: *mut crate::leanh::LeanObject,
    mut v_name_829_: *mut crate::leanh::LeanObject,
    mut v___y_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
    mut v___y_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_833_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__2_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_(v___f_828_, v_name_829_, v___y_830_, v___y_831_);
    crate::leanh::lean_dec(v___y_831_);
    crate::leanh::lean_dec_ref(v___y_830_);
    return v_res_833_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_846_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_847_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_848_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_849_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__6_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_;
    v___x_850_ = l_Lake_registerOrderedTagAttribute(v___x_847_, v___x_848_, v___f_846_, v___x_849_);
    return v___x_850_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2____boxed(
    mut v_a_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
    return v_res_852_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_853_: *mut crate::leanh::LeanObject,
    mut v_msg_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v_msg_854_, v___y_855_, v___y_856_);
    return v___x_858_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_859_: *mut crate::leanh::LeanObject,
    mut v_msg_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1(v_00_u03b1_859_, v_msg_860_, v___y_861_, v___y_862_);
    crate::leanh::lean_dec(v___y_862_);
    crate::leanh::lean_dec_ref(v___y_861_);
    return v_res_864_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_874_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_875_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_;
    v___x_876_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_;
    v___x_877_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_;
    v___x_878_ = l_Lake_registerOrderedTagAttribute(v___x_875_, v___x_876_, v___f_874_, v___x_877_);
    return v___x_878_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2____boxed(
    mut v_a_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_880_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
    return v_res_880_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_890_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_891_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_;
    v___x_892_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_;
    v___x_893_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_;
    v___x_894_ = l_Lake_registerOrderedTagAttribute(v___x_891_, v___x_892_, v___f_890_, v___x_893_);
    return v___x_894_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2____boxed(
    mut v_a_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
    return v_res_896_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_906_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_907_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_;
    v___x_908_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_;
    v___x_909_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_;
    v___x_910_ = l_Lake_registerOrderedTagAttribute(v___x_907_, v___x_908_, v___f_906_, v___x_909_);
    return v___x_910_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2____boxed(
    mut v_a_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_912_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
    return v_res_912_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_922_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_923_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_;
    v___x_924_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_;
    v___x_925_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_;
    v___x_926_ = l_Lake_registerOrderedTagAttribute(v___x_923_, v___x_924_, v___f_922_, v___x_925_);
    return v___x_926_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2____boxed(
    mut v_a_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
    return v_res_928_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_938_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_939_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_;
    v___x_940_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_;
    v___x_941_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_;
    v___x_942_ = l_Lake_registerOrderedTagAttribute(v___x_939_, v___x_940_, v___f_938_, v___x_941_);
    return v___x_942_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2____boxed(
    mut v_a_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_944_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
    return v_res_944_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_954_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_955_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_;
    v___x_956_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_;
    v___x_957_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_;
    v___x_958_ = l_Lake_registerOrderedTagAttribute(v___x_955_, v___x_956_, v___f_954_, v___x_957_);
    return v___x_958_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2____boxed(
    mut v_a_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
    return v_res_960_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(
    mut v_name_961_: *mut crate::leanh::LeanObject,
    mut v_env_962_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    v___x_963_ = l_Lake_targetAttr;
    v___x_964_ = l_Lake_OrderedTagAttribute_hasTag(v___x_963_, v_env_962_, v_name_961_);
    return v___x_964_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(
    mut v_name_965_: *mut crate::leanh::LeanObject,
    mut v_env_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_967_: u8 = 0;
    let mut v_r_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v_name_965_, v_env_966_);
    crate::leanh::lean_dec(v_name_965_);
    v_r_968_ = crate::leanh::lean_box((v_res_967_) as usize);
    return v_r_968_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
    return v___x_971_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(
    mut v___f_972_: *mut crate::leanh::LeanObject,
    mut v_name_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_990_: u8 = 0;
    let mut v_a_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_977_ = crate::leanh::lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_977_, 0, v_name_973_);
                v___x_978_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_972_, v___f_977_, v___y_974_, v___y_975_);
                if crate::leanh::lean_obj_tag(v___x_978_) == 0 {
                    v_a_979_ = crate::leanh::lean_ctor_get(v___x_978_, 0);
                    v_isSharedCheck_990_ = (!crate::leanh::lean_is_exclusive(v___x_978_)) as u8;
                    if v_isSharedCheck_990_ == 0 {
                        v___x_981_ = v___x_978_;
                        v_isShared_982_ = v_isSharedCheck_990_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_979_);
                        crate::leanh::lean_dec(v___x_978_);
                        v___x_981_ = crate::leanh::lean_box(0);
                        v_isShared_982_ = v_isSharedCheck_990_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_991_ = crate::leanh::lean_ctor_get(v___x_978_, 0);
                    v_isSharedCheck_998_ = (!crate::leanh::lean_is_exclusive(v___x_978_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_993_ = v___x_978_;
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_991_);
                        crate::leanh::lean_dec(v___x_978_);
                        v___x_993_ = crate::leanh::lean_box(0);
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_983_ = (crate::leanh::lean_unbox(v_a_979_) as u8);
                crate::leanh::lean_dec(v_a_979_);
                if v___x_983_ == 0 {
                    crate::leanh::lean_del_object(v___x_981_);
                    v___x_984_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_);
                    v___x_985_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_984_, v___y_974_, v___y_975_);
                    return v___x_985_;
                } else {
                    v___x_986_ = crate::leanh::lean_box(0);
                    if v_isShared_982_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_981_, 0, v___x_986_);
                        v___x_988_ = v___x_981_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
                        v___x_988_ = v_reuseFailAlloc_989_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_988_;
            }
            3 => {
                if v_isShared_994_ == 0 {
                    v___x_996_ = v___x_993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(
    mut v___f_999_: *mut crate::leanh::LeanObject,
    mut v_name_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1004_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_(v___f_999_, v_name_1000_, v___y_1001_, v___y_1002_);
    crate::leanh::lean_dec(v___y_1002_);
    crate::leanh::lean_dec_ref(v___y_1001_);
    return v_res_1004_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1016_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1017_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1018_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1019_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_;
    v___x_1020_ =
        l_Lake_registerOrderedTagAttribute(v___x_1017_, v___x_1018_, v___f_1016_, v___x_1019_);
    return v___x_1020_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2____boxed(
    mut v_a_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1022_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
    return v_res_1022_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(
    mut v_name_1023_: *mut crate::leanh::LeanObject,
    mut v_env_1024_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_1026_: u8 = 0;
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1029_ = l_Lake_scriptAttr;
                crate::leanh::lean_inc_ref(v_env_1024_);
                v___x_1030_ =
                    l_Lake_OrderedTagAttribute_hasTag(v___x_1029_, v_env_1024_, v_name_1023_);
                if v___x_1030_ == 0 {
                    v___x_1031_ = l_Lake_leanExeAttr;
                    crate::leanh::lean_inc_ref(v_env_1024_);
                    v___x_1032_ =
                        l_Lake_OrderedTagAttribute_hasTag(v___x_1031_, v_env_1024_, v_name_1023_);
                    v___y_1026_ = v___x_1032_;
                    state = 1;
                    continue;
                } else {
                    v___y_1026_ = v___x_1030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1026_ == 0 {
                    v___x_1027_ = l_Lake_leanLibAttr;
                    v___x_1028_ =
                        l_Lake_OrderedTagAttribute_hasTag(v___x_1027_, v_env_1024_, v_name_1023_);
                    return v___x_1028_;
                } else {
                    crate::leanh::lean_dec_ref(v_env_1024_);
                    return v___y_1026_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(
    mut v_name_1033_: *mut crate::leanh::LeanObject,
    mut v_env_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1035_: u8 = 0;
    let mut v_r_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v_name_1033_, v_env_1034_);
    crate::leanh::lean_dec(v_name_1033_);
    v_r_1036_ = crate::leanh::lean_box((v_res_1035_) as usize);
    return v_r_1036_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
    return v___x_1039_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(
    mut v___f_1040_: *mut crate::leanh::LeanObject,
    mut v_name_1041_: *mut crate::leanh::LeanObject,
    mut v___y_1042_: *mut crate::leanh::LeanObject,
    mut v___y_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1050_: u8 = 0;
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v_a_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1045_ = crate::leanh::lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_1045_, 0, v_name_1041_);
                v___x_1046_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_1040_, v___f_1045_, v___y_1042_, v___y_1043_);
                if crate::leanh::lean_obj_tag(v___x_1046_) == 0 {
                    v_a_1047_ = crate::leanh::lean_ctor_get(v___x_1046_, 0);
                    v_isSharedCheck_1058_ = (!crate::leanh::lean_is_exclusive(v___x_1046_)) as u8;
                    if v_isSharedCheck_1058_ == 0 {
                        v___x_1049_ = v___x_1046_;
                        v_isShared_1050_ = v_isSharedCheck_1058_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1047_);
                        crate::leanh::lean_dec(v___x_1046_);
                        v___x_1049_ = crate::leanh::lean_box(0);
                        v_isShared_1050_ = v_isSharedCheck_1058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1059_ = crate::leanh::lean_ctor_get(v___x_1046_, 0);
                    v_isSharedCheck_1066_ = (!crate::leanh::lean_is_exclusive(v___x_1046_)) as u8;
                    if v_isSharedCheck_1066_ == 0 {
                        v___x_1061_ = v___x_1046_;
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1059_);
                        crate::leanh::lean_dec(v___x_1046_);
                        v___x_1061_ = crate::leanh::lean_box(0);
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1051_ = (crate::leanh::lean_unbox(v_a_1047_) as u8);
                crate::leanh::lean_dec(v_a_1047_);
                if v___x_1051_ == 0 {
                    crate::leanh::lean_del_object(v___x_1049_);
                    v___x_1052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_);
                    v___x_1053_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_1052_, v___y_1042_, v___y_1043_);
                    return v___x_1053_;
                } else {
                    v___x_1054_ = crate::leanh::lean_box(0);
                    if v_isShared_1050_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1049_, 0, v___x_1054_);
                        v___x_1056_ = v___x_1049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
                        v___x_1056_ = v_reuseFailAlloc_1057_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1056_;
            }
            3 => {
                if v_isShared_1062_ == 0 {
                    v___x_1064_ = v___x_1061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
                    v___x_1064_ = v_reuseFailAlloc_1065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(
    mut v___f_1067_: *mut crate::leanh::LeanObject,
    mut v_name_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_(v___f_1067_, v_name_1068_, v___y_1069_, v___y_1070_);
    crate::leanh::lean_dec(v___y_1070_);
    crate::leanh::lean_dec_ref(v___y_1069_);
    return v_res_1072_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1084_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1085_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1086_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1087_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_;
    v___x_1088_ =
        l_Lake_registerOrderedTagAttribute(v___x_1085_, v___x_1086_, v___f_1084_, v___x_1087_);
    return v___x_1088_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2____boxed(
    mut v_a_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
    return v_res_1090_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(
    mut v_name_1091_: *mut crate::leanh::LeanObject,
    mut v_env_1092_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    v___x_1093_ = l_Lake_scriptAttr;
    crate::leanh::lean_inc_ref(v_env_1092_);
    v___x_1094_ = l_Lake_OrderedTagAttribute_hasTag(v___x_1093_, v_env_1092_, v_name_1091_);
    if v___x_1094_ == 0 {
        let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: u8 = 0;
        v___x_1095_ = l_Lake_leanExeAttr;
        v___x_1096_ = l_Lake_OrderedTagAttribute_hasTag(v___x_1095_, v_env_1092_, v_name_1091_);
        return v___x_1096_;
    } else {
        crate::leanh::lean_dec_ref(v_env_1092_);
        return v___x_1094_;
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(
    mut v_name_1097_: *mut crate::leanh::LeanObject,
    mut v_env_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1099_: u8 = 0;
    let mut v_r_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1099_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v_name_1097_, v_env_1098_);
    crate::leanh::lean_dec(v_name_1097_);
    v_r_1100_ = crate::leanh::lean_box((v_res_1099_) as usize);
    return v_r_1100_;
}
pub unsafe fn _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
    return v___x_1103_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(
    mut v___f_1104_: *mut crate::leanh::LeanObject,
    mut v_name_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v_a_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1126_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1109_ = crate::leanh::lean_alloc_closure(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_1109_, 0, v_name_1105_);
                v___x_1110_ = l_Functor_mapRev___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__0___redArg(v___f_1104_, v___f_1109_, v___y_1106_, v___y_1107_);
                if crate::leanh::lean_obj_tag(v___x_1110_) == 0 {
                    v_a_1111_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                    v_isSharedCheck_1122_ = (!crate::leanh::lean_is_exclusive(v___x_1110_)) as u8;
                    if v_isSharedCheck_1122_ == 0 {
                        v___x_1113_ = v___x_1110_;
                        v_isShared_1114_ = v_isSharedCheck_1122_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1111_);
                        crate::leanh::lean_dec(v___x_1110_);
                        v___x_1113_ = crate::leanh::lean_box(0);
                        v_isShared_1114_ = v_isSharedCheck_1122_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1123_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                    v_isSharedCheck_1130_ = (!crate::leanh::lean_is_exclusive(v___x_1110_)) as u8;
                    if v_isSharedCheck_1130_ == 0 {
                        v___x_1125_ = v___x_1110_;
                        v_isShared_1126_ = v_isSharedCheck_1130_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1123_);
                        crate::leanh::lean_dec(v___x_1110_);
                        v___x_1125_ = crate::leanh::lean_box(0);
                        v_isShared_1126_ = v_isSharedCheck_1130_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1115_ = (crate::leanh::lean_unbox(v_a_1111_) as u8);
                crate::leanh::lean_dec(v_a_1111_);
                if v___x_1115_ == 0 {
                    crate::leanh::lean_del_object(v___x_1113_);
                    v___x_1116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2__once), _init_l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_);
                    v___x_1117_ = l_Lean_throwError___at___00__private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2__spec__1___redArg(v___x_1116_, v___y_1106_, v___y_1107_);
                    return v___x_1117_;
                } else {
                    v___x_1118_ = crate::leanh::lean_box(0);
                    if v_isShared_1114_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1113_, 0, v___x_1118_);
                        v___x_1120_ = v___x_1113_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
                        v___x_1120_ = v_reuseFailAlloc_1121_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1120_;
            }
            3 => {
                if v_isShared_1126_ == 0 {
                    v___x_1128_ = v___x_1125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
                    v___x_1128_ = v_reuseFailAlloc_1129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(
    mut v___f_1131_: *mut crate::leanh::LeanObject,
    mut v_name_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___lam__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_(v___f_1131_, v_name_1132_, v___y_1133_, v___y_1134_);
    crate::leanh::lean_dec(v___y_1134_);
    crate::leanh::lean_dec_ref(v___y_1133_);
    return v_res_1136_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1148_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1149_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1150_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__3_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1151_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__5_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_;
    v___x_1152_ =
        l_Lake_registerOrderedTagAttribute(v___x_1149_, v___x_1150_, v___f_1148_, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2____boxed(
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
    return v_res_1154_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1164_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_1165_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_;
    v___x_1166_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_;
    v___x_1167_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_;
    v___x_1168_ =
        l_Lake_registerOrderedTagAttribute(v___x_1165_, v___x_1166_, v___f_1164_, v___x_1167_);
    return v___x_1168_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2____boxed(
    mut v_a_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1170_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
    return v_res_1170_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1180_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_1181_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_;
    v___x_1182_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_;
    v___x_1183_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_;
    v___x_1184_ =
        l_Lake_registerOrderedTagAttribute(v___x_1181_, v___x_1182_, v___f_1180_, v___x_1183_);
    return v___x_1184_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2____boxed(
    mut v_a_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
    return v_res_1186_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1196_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__0_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_;
    v___x_1197_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__1_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_;
    v___x_1198_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__2_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_;
    v___x_1199_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn___closed__4_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_;
    v___x_1200_ =
        l_Lake_registerOrderedTagAttribute(v___x_1197_, v___x_1198_, v___f_1196_, v___x_1199_);
    return v___x_1200_;
}
pub unsafe fn l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2____boxed(
    mut v_a_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1202_ = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
    return v_res_1202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_AttributesCore(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3272526623____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_packageAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_packageAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2767938986____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_packageDepAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_packageDepAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1620868245____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_postUpdateAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_postUpdateAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3623187058____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_scriptAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_scriptAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2501670873____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_defaultScriptAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_defaultScriptAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1207319905____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_leanLibAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_leanLibAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3537518125____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_leanExeAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_leanExeAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_914944953____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_externLibAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_externLibAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2342384104____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_inputFileAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_inputFileAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2316908844____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_inputDirAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_inputDirAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_2750287618____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_targetAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_targetAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_736500823____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_defaultTargetAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_defaultTargetAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3062214538____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_testDriverAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_testDriverAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_587736814____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_lintDriverAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_lintDriverAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_3793002438____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_moduleFacetAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_moduleFacetAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1817870049____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_packageFacetAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_packageFacetAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_AttributesCore_0__Lake_initFn_00___x40_Lake_DSL_AttributesCore_1787873690____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_libraryFacetAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_libraryFacetAttr);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_AttributesCore(
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
pub unsafe fn initialize_Lake_DSL_AttributesCore(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_OrderedTagAttribute(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_AttributesCore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_AttributesCore(builtin);
}
