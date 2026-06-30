// Lean compiler output
// Module: Lean.Elab.AutoBound
// Imports: Lean.Meta.Hint
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_is_valid_pos,
    lean_string_utf8_byte_size, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::Defs::l_String_instInhabitedSlice;
use crate::r#gen::Init::Data::String::Substring::l_Substring_Raw_nextn;
use crate::r#gen::Init::Meta::Defs::l_Lean_isSubScriptAlnum;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Hint::{
    initialize_Lean_Meta_Hint, runtime_initialize_Lean_Meta_Hint,
};
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 117, 116, 111, 73, 109, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15951281942633481588 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanStringObject<323> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 323, m_capacity: 323, m_length: 319, m_data: [85, 110, 98, 111, 117, 110, 100, 32, 108, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 104, 101, 97, 100, 101, 114, 115, 32, 98, 101, 99, 111, 109, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 46, 32, 73, 110, 32, 34, 114, 101, 108, 97, 120, 101, 100, 34, 32, 109, 111, 100, 101, 32, 40, 100, 101, 102, 97, 117, 108, 116, 41, 44, 32, 97, 110, 121, 32, 97, 116, 111, 109, 105, 99, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 105, 115, 32, 101, 108, 105, 103, 105, 98, 108, 101, 44, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 111, 110, 108, 121, 32, 115, 105, 110, 103, 108, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 32, 102, 111, 108, 108, 111, 119, 101, 100, 32, 98, 121, 32, 110, 117, 109, 101, 114, 105, 99, 32, 100, 105, 103, 105, 116, 115, 32, 97, 114, 101, 32, 101, 108, 105, 103, 105, 98, 108, 101, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 96, 100, 101, 102, 32, 102, 32, 40, 120, 32, 58, 32, 86, 101, 99, 116, 111, 114, 32, 206, 177, 32, 110, 41, 32, 58, 32, 86, 101, 99, 116, 111, 114, 32, 206, 177, 32, 110, 32, 58, 61, 96, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 115, 32, 116, 104, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 123, 206, 177, 32, 110, 125, 46, 0]};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14295638553363301127 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_autoImplicit: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [114, 101, 108, 97, 120, 101, 100, 65, 117, 116, 111, 73, 109, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12024965962538157967 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value: leanh::LeanStringObject<135> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 135, m_capacity: 135, m_length: 134, m_data: [87, 104, 101, 110, 32, 34, 114, 101, 108, 97, 120, 101, 100, 34, 32, 109, 111, 100, 101, 32, 105, 115, 32, 101, 110, 97, 98, 108, 101, 100, 44, 32, 97, 110, 121, 32, 97, 116, 111, 109, 105, 99, 32, 110, 111, 110, 101, 109, 112, 116, 121, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 105, 115, 32, 101, 108, 105, 103, 105, 98, 108, 101, 32, 102, 111, 114, 32, 97, 117, 116, 111, 32, 98, 111, 117, 110, 100, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 108, 111, 99, 97, 108, 115, 32, 40, 115, 101, 101, 32, 111, 112, 116, 105, 111, 110, 32, 96, 97, 117, 116, 111, 73, 109, 112, 108, 105, 99, 105, 116, 96, 41, 46, 0]};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14454808432271789644 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_relaxedAutoImplicit: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0_value:
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
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1_value:
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
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2_value:
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
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        73, 116, 32, 105, 115, 32, 110, 111, 116, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32,
        116, 111, 32, 116, 114, 101, 97, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3_value:
    leanh::LeanStringObject<85> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 85,
    m_capacity: 85,
    m_length: 84,
    m_data: [
        96, 32, 97, 115, 32, 97, 110, 32, 105, 109, 112, 108, 105, 99, 105, 116, 108, 121, 32, 98,
        111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 101, 114, 101, 32,
        98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 32, 96, 97, 117, 116, 111, 73, 109, 112,
        108, 105, 99, 105, 116, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 115, 101,
        116, 32, 116, 111, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__5_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__6_value)
            as *mut leanh::LeanObject,
        15761733860085307253 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8_value:
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
    m_data: [96, 46, 0],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10_value:
    leanh::LeanStringObject<125> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 125,
    m_capacity: 125,
    m_length: 124,
    m_data: [
        96, 32, 97, 115, 32, 97, 110, 32, 105, 109, 112, 108, 105, 99, 105, 116, 108, 121, 32, 98,
        111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 101, 114, 101, 32,
        98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 104, 97, 115, 32, 109, 117, 108, 116,
        105, 112, 108, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 32, 119, 104, 105,
        108, 101, 32, 116, 104, 101, 32, 96, 114, 101, 108, 97, 120, 101, 100, 65, 117, 116, 111,
        73, 109, 112, 108, 105, 99, 105, 116, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115,
        32, 115, 101, 116, 32, 116, 111, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedAutoBoundImplicitContext: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(
    mut v_name_272_: *mut leanh::LeanObject,
    mut v_decl_273_: *mut leanh::LeanObject,
    mut v_ref_274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_285_: u8 = 0;
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_290_: u8 = 0;
    let mut v_unused_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_276_ = leanh::lean_ctor_get(v_decl_273_, 0);
                v_descr_277_ = leanh::lean_ctor_get(v_decl_273_, 1);
                v_deprecation_x3f_278_ = leanh::lean_ctor_get(v_decl_273_, 2);
                v___x_279_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_280_ = (leanh::lean_unbox(v_defValue_276_) as u8);
                leanh::lean_ctor_set_uint8(v___x_279_, 0 as u32, v___x_280_);
                leanh::lean_inc(v_deprecation_x3f_278_);
                leanh::lean_inc_ref(v_descr_277_);
                leanh::lean_inc_n(v_name_272_, 2);
                v___x_281_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_281_, 0, v_name_272_);
                leanh::lean_ctor_set(v___x_281_, 1, v_ref_274_);
                leanh::lean_ctor_set(v___x_281_, 2, v___x_279_);
                leanh::lean_ctor_set(v___x_281_, 3, v_descr_277_);
                leanh::lean_ctor_set(v___x_281_, 4, v_deprecation_x3f_278_);
                v___x_282_ = lean_register_option(v_name_272_, v___x_281_);
                if leanh::lean_obj_tag(v___x_282_) == 0 {
                    v_isSharedCheck_290_ = (!leanh::lean_is_exclusive(v___x_282_)) as u8;
                    if v_isSharedCheck_290_ == 0 {
                        v_unused_291_ = leanh::lean_ctor_get(v___x_282_, 0);
                        leanh::lean_dec(v_unused_291_);
                        v___x_284_ = v___x_282_;
                        v_isShared_285_ = v_isSharedCheck_290_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_282_);
                        v___x_284_ = leanh::lean_box(0);
                        v_isShared_285_ = v_isSharedCheck_290_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_272_);
                    v_a_292_ = leanh::lean_ctor_get(v___x_282_, 0);
                    v_isSharedCheck_299_ = (!leanh::lean_is_exclusive(v___x_282_)) as u8;
                    if v_isSharedCheck_299_ == 0 {
                        v___x_294_ = v___x_282_;
                        v_isShared_295_ = v_isSharedCheck_299_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_292_);
                        leanh::lean_dec(v___x_282_);
                        v___x_294_ = leanh::lean_box(0);
                        v_isShared_295_ = v_isSharedCheck_299_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_276_);
                v___x_286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_286_, 0, v_name_272_);
                leanh::lean_ctor_set(v___x_286_, 1, v_defValue_276_);
                if v_isShared_285_ == 0 {
                    leanh::lean_ctor_set(v___x_284_, 0, v___x_286_);
                    v___x_288_ = v___x_284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_289_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
                    v___x_288_ = v_reuseFailAlloc_289_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_288_;
            }
            3 => {
                if v_isShared_295_ == 0 {
                    v___x_297_ = v___x_294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
                    v___x_297_ = v_reuseFailAlloc_298_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_300_: *mut leanh::LeanObject,
    mut v_decl_301_: *mut leanh::LeanObject,
    mut v_ref_302_: *mut leanh::LeanObject,
    mut v_a_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v_name_300_, v_decl_301_, v_ref_302_);
    leanh::lean_dec_ref(v_decl_301_);
    return v_res_304_;
}
pub unsafe fn l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_;
    v___x_322_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_;
    v___x_323_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_;
    v___x_324_ = l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v___x_321_, v___x_322_, v___x_323_);
    return v___x_324_;
}
pub unsafe fn l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4____boxed(
    mut v_a_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
    return v_res_326_;
}
pub unsafe fn l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_;
    v___x_342_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_;
    v___x_343_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_;
    v___x_344_ = l_Lean_Option_register___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4__spec__0(v___x_341_, v___x_342_, v___x_343_);
    return v___x_344_;
}
pub unsafe fn l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4____boxed(
    mut v_a_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
    return v_res_346_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(
    mut v_msg_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = l_String_instInhabitedSlice;
    v___x_349_ = lean_panic_fn_borrowed(v___x_348_, v_msg_347_);
    return v___x_349_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(
    mut v_s_350_: *mut leanh::LeanObject,
    mut v_pos_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: u8 = 0;
    let mut v___y_363_: u8 = 0;
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: u8 = 0;
    let mut v___x_367_: u32 = 0;
    let mut v___y_369_: u8 = 0;
    let mut v___x_370_: u8 = 0;
    let mut v___x_371_: u32 = 0;
    let mut v___x_372_: u8 = 0;
    let mut v___x_373_: u32 = 0;
    let mut v___x_374_: u8 = 0;
    let mut v___x_375_: u32 = 0;
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: u32 = 0;
    let mut v___x_378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_352_ = leanh::lean_ctor_get(v_s_350_, 0);
                v_startInclusive_353_ = leanh::lean_ctor_get(v_s_350_, 1);
                v_endExclusive_354_ = leanh::lean_ctor_get(v_s_350_, 2);
                v___x_355_ = lean_nat_add(v_startInclusive_353_, v_pos_351_);
                v___x_364_ = leanh::lean_unsigned_to_nat(0);
                v___x_365_ = lean_nat_sub(v_endExclusive_354_, v___x_355_);
                v___x_366_ = lean_nat_dec_eq(v___x_364_, v___x_365_);
                leanh::lean_dec(v___x_365_);
                if v___x_366_ == 0 {
                    v___x_367_ = lean_string_utf8_get_fast(v_str_352_, v___x_355_);
                    v___x_375_ = 48;
                    v___x_376_ = lean_uint32_dec_le(v___x_375_, v___x_367_);
                    if v___x_376_ == 0 {
                        v___y_369_ = v___x_376_;
                        state = 3;
                        continue;
                    } else {
                        v___x_377_ = 57;
                        v___x_378_ = lean_uint32_dec_le(v___x_367_, v___x_377_);
                        v___y_369_ = v___x_378_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_355_);
                    return v_pos_351_;
                }
            }
            1 => {
                v___x_357_ = lean_string_utf8_next_fast(v_str_352_, v___x_355_);
                v___x_358_ = lean_nat_sub(v___x_357_, v___x_355_);
                leanh::lean_dec(v___x_355_);
                v___x_359_ = lean_nat_add(v_pos_351_, v___x_358_);
                leanh::lean_dec(v___x_358_);
                v___x_360_ = lean_nat_dec_lt(v_pos_351_, v___x_359_);
                if v___x_360_ == 0 {
                    leanh::lean_dec(v___x_359_);
                    return v_pos_351_;
                } else {
                    leanh::lean_dec(v_pos_351_);
                    v_pos_351_ = v___x_359_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_363_ == 0 {
                    leanh::lean_dec(v___x_355_);
                    return v_pos_351_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_369_ == 0 {
                    v___x_370_ = l_Lean_isSubScriptAlnum(v___x_367_);
                    if v___x_370_ == 0 {
                        v___x_371_ = 95;
                        v___x_372_ = lean_uint32_dec_eq(v___x_367_, v___x_371_);
                        if v___x_372_ == 0 {
                            v___x_373_ = 39;
                            v___x_374_ = lean_uint32_dec_eq(v___x_367_, v___x_373_);
                            v___y_363_ = v___x_374_;
                            state = 2;
                            continue;
                        } else {
                            v___y_363_ = v___x_372_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_363_ = v___x_370_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0___boxed(
    mut v_s_379_: *mut leanh::LeanObject,
    mut v_pos_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_381_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v_s_379_, v_pos_380_);
    leanh::lean_dec_ref(v_s_379_);
    return v_res_381_;
}
pub unsafe fn _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__2;
    v___x_386_ = leanh::lean_unsigned_to_nat(14);
    v___x_387_ = leanh::lean_unsigned_to_nat(22);
    v___x_388_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__1;
    v___x_389_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__0;
    v___x_390_ =
        l_mkPanicMessageWithDecl(v___x_389_, v___x_388_, v___x_387_, v___x_386_, v___x_385_);
    return v___x_390_;
}
pub unsafe fn l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(
    mut v_s_391_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: u8 = 0;
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: u8 = 0;
    let mut v___x_411_: u8 = 0;
    let mut v___x_412_: u8 = 0;
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_405_ = leanh::lean_unsigned_to_nat(0);
                v___x_406_ = lean_string_utf8_byte_size(v_s_391_);
                leanh::lean_inc_ref(v_s_391_);
                v___x_407_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_407_, 0, v_s_391_);
                leanh::lean_ctor_set(v___x_407_, 1, v___x_405_);
                leanh::lean_ctor_set(v___x_407_, 2, v___x_406_);
                v___x_408_ = leanh::lean_unsigned_to_nat(1);
                v___x_409_ = l_Substring_Raw_nextn(v___x_407_, v___x_408_, v___x_405_);
                leanh::lean_dec_ref_known(v___x_407_, 3);
                v___x_410_ = lean_string_is_valid_pos(v_s_391_, v___x_409_);
                if v___x_410_ == 0 {
                    leanh::lean_dec(v___x_409_);
                    leanh::lean_dec_ref(v_s_391_);
                    state = 2;
                    continue;
                } else {
                    v___x_411_ = lean_string_is_valid_pos(v_s_391_, v___x_406_);
                    if v___x_411_ == 0 {
                        leanh::lean_dec(v___x_409_);
                        leanh::lean_dec_ref(v_s_391_);
                        state = 2;
                        continue;
                    } else {
                        v___x_412_ = lean_nat_dec_le(v___x_409_, v___x_406_);
                        if v___x_412_ == 0 {
                            leanh::lean_dec(v___x_409_);
                            leanh::lean_dec_ref(v_s_391_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_409_);
                            v___x_413_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_413_, 0, v_s_391_);
                            leanh::lean_ctor_set(v___x_413_, 1, v___x_409_);
                            leanh::lean_ctor_set(v___x_413_, 2, v___x_406_);
                            v___y_393_ = v___x_413_;
                            v_startInclusive_394_ = v___x_409_;
                            v_endExclusive_395_ = v___x_406_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_396_ = leanh::lean_unsigned_to_nat(0);
                v___x_397_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__0(v___y_393_, v___x_396_);
                leanh::lean_dec_ref(v___y_393_);
                v___x_398_ = lean_nat_sub(v_endExclusive_395_, v_startInclusive_394_);
                leanh::lean_dec(v_startInclusive_394_);
                leanh::lean_dec(v_endExclusive_395_);
                v___x_399_ = lean_nat_dec_eq(v___x_397_, v___x_398_);
                leanh::lean_dec(v___x_398_);
                leanh::lean_dec(v___x_397_);
                return v___x_399_;
            }
            2 => {
                v___x_401_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3_once), _init_l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___closed__3);
                v___x_402_ = l_panic___at___00__private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix_spec__1(v___x_401_);
                v_startInclusive_403_ = leanh::lean_ctor_get(v___x_402_, 1);
                leanh::lean_inc(v_startInclusive_403_);
                v_endExclusive_404_ = leanh::lean_ctor_get(v___x_402_, 2);
                leanh::lean_inc(v_endExclusive_404_);
                v___y_393_ = v___x_402_;
                v_startInclusive_394_ = v_startInclusive_403_;
                v_endExclusive_395_ = v_endExclusive_404_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix___boxed(
    mut v_s_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_415_: u8 = 0;
    let mut v_r_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_s_414_);
    v_r_416_ = leanh::lean_box((v_res_415_) as usize);
    return v_r_416_;
}
pub unsafe fn _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__1;
    v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
    return v___x_422_;
}
pub unsafe fn _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__3;
    v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
    return v___x_425_;
}
pub unsafe fn _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__8;
    v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
    return v___x_433_;
}
pub unsafe fn _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__10;
    v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
    return v___x_436_;
}
pub unsafe fn l_Lean_Elab_checkValidAutoBoundImplicitName(
    mut v_n_437_: *mut leanh::LeanObject,
    mut v_allowed_438_: u8,
    mut v_relaxed_439_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_443_: u8 = 0;
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: u8 = 0;
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_437_) == 1 {
                    v_pre_468_ = leanh::lean_ctor_get(v_n_437_, 0);
                    if leanh::lean_obj_tag(v_pre_468_) == 0 {
                        v_str_469_ = leanh::lean_ctor_get(v_n_437_, 1);
                        v___x_470_ = lean_string_utf8_byte_size(v_str_469_);
                        v___x_471_ = leanh::lean_unsigned_to_nat(0);
                        v___x_472_ = lean_nat_dec_eq(v___x_470_, v___x_471_);
                        if v___x_472_ == 0 {
                            if v_allowed_438_ == 0 {
                                v___y_443_ = v_allowed_438_;
                                state = 2;
                                continue;
                            } else {
                                if v_relaxed_439_ == 0 {
                                    leanh::lean_inc_ref(v_str_469_);
                                    v___x_473_ = l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(v_str_469_);
                                    if v___x_473_ == 0 {
                                        v___y_443_ = v___x_473_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref_known(v_n_437_, 2);
                                        v___x_474_ =
                                            leanh::lean_box((v_allowed_438_) as usize);
                                        v___x_475_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_475_, 0, v___x_474_);
                                        return v___x_475_;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v_n_437_, 2);
                                    v___x_476_ = leanh::lean_box((v_allowed_438_) as usize);
                                    v___x_477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_477_, 0, v___x_476_);
                                    return v___x_477_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_n_437_, 2);
                            v___x_478_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0;
                            return v___x_478_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_n_437_, 2);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_n_437_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_441_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__0;
                return v___x_441_;
            }
            2 => {
                if v_allowed_438_ == 0 {
                    v___x_444_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once
                        ),
                        _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2,
                    );
                    v___x_445_ = l_Lean_MessageData_ofConstName(v_n_437_, v___y_443_);
                    v___x_446_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_446_, 0, v___x_444_);
                    leanh::lean_ctor_set(v___x_446_, 1, v___x_445_);
                    v___x_447_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4_once
                        ),
                        _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__4,
                    );
                    v___x_448_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_448_, 0, v___x_446_);
                    leanh::lean_ctor_set(v___x_448_, 1, v___x_447_);
                    v___x_449_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7;
                    v___x_450_ = l_Lean_MessageData_ofConstName(v___x_449_, v___y_443_);
                    v___x_451_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_451_, 0, v___x_448_);
                    leanh::lean_ctor_set(v___x_451_, 1, v___x_450_);
                    v___x_452_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once
                        ),
                        _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9,
                    );
                    v___x_453_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_453_, 0, v___x_451_);
                    leanh::lean_ctor_set(v___x_453_, 1, v___x_452_);
                    v___x_454_ = l_Lean_MessageData_note(v___x_453_);
                    v___x_455_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_455_, 0, v___x_454_);
                    return v___x_455_;
                } else {
                    v___x_456_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2_once
                        ),
                        _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__2,
                    );
                    v___x_457_ = l_Lean_MessageData_ofConstName(v_n_437_, v___y_443_);
                    v___x_458_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_458_, 0, v___x_456_);
                    leanh::lean_ctor_set(v___x_458_, 1, v___x_457_);
                    v___x_459_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11_once
                        ),
                        _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__11,
                    );
                    v___x_460_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_460_, 0, v___x_458_);
                    leanh::lean_ctor_set(v___x_460_, 1, v___x_459_);
                    v___x_461_ = l_Lean_Elab_checkValidAutoBoundImplicitName___closed__7;
                    v___x_462_ = l_Lean_MessageData_ofConstName(v___x_461_, v___y_443_);
                    v___x_463_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_463_, 0, v___x_460_);
                    leanh::lean_ctor_set(v___x_463_, 1, v___x_462_);
                    v___x_464_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9_once
                        ),
                        _init_l_Lean_Elab_checkValidAutoBoundImplicitName___closed__9,
                    );
                    v___x_465_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_465_, 0, v___x_463_);
                    leanh::lean_ctor_set(v___x_465_, 1, v___x_464_);
                    v___x_466_ = l_Lean_MessageData_note(v___x_465_);
                    v___x_467_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_467_, 0, v___x_466_);
                    return v___x_467_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkValidAutoBoundImplicitName___boxed(
    mut v_n_479_: *mut leanh::LeanObject,
    mut v_allowed_480_: *mut leanh::LeanObject,
    mut v_relaxed_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowed_boxed_482_: u8 = 0;
    let mut v_relaxed_boxed_483_: u8 = 0;
    let mut v_res_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowed_boxed_482_ = (leanh::lean_unbox(v_allowed_480_) as u8);
    v_relaxed_boxed_483_ = (leanh::lean_unbox(v_relaxed_481_) as u8);
    v_res_484_ = l_Lean_Elab_checkValidAutoBoundImplicitName(
        v_n_479_,
        v_allowed_boxed_482_,
        v_relaxed_boxed_483_,
    );
    return v_res_484_;
}
pub unsafe fn l_Lean_Elab_isValidAutoBoundLevelName(
    mut v_n_485_: *mut leanh::LeanObject,
    mut v_relaxed_486_: u8,
) -> u8 {
    let mut v_pre_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_490_: u8 = 0;
    let mut v___x_491_: u8 = 0;
    let mut v___y_493_: u32 = 0;
    let mut v___x_494_: u32 = 0;
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: u32 = 0;
    let mut v___x_497_: u8 = 0;
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u32 = 0;
    let mut v_val_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u32 = 0;
    let mut v___x_506_: u8 = 0;
    let mut v___x_507_: u8 = 0;
    let mut v___x_508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_485_) == 1 {
                    v_pre_487_ = leanh::lean_ctor_get(v_n_485_, 0);
                    leanh::lean_inc(v_pre_487_);
                    v_str_488_ = leanh::lean_ctor_get(v_n_485_, 1);
                    leanh::lean_inc_ref(v_str_488_);
                    leanh::lean_dec_ref_known(v_n_485_, 2);
                    if leanh::lean_obj_tag(v_pre_487_) == 0 {
                        v___x_498_ = lean_string_utf8_byte_size(v_str_488_);
                        v___x_499_ = leanh::lean_unsigned_to_nat(0);
                        v___x_500_ = lean_nat_dec_eq(v___x_498_, v___x_499_);
                        if v___x_500_ == 0 {
                            if v_relaxed_486_ == 0 {
                                leanh::lean_inc_ref(v_str_488_);
                                v___x_501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                leanh::lean_ctor_set(v___x_501_, 0, v_str_488_);
                                leanh::lean_ctor_set(v___x_501_, 1, v___x_499_);
                                leanh::lean_ctor_set(v___x_501_, 2, v___x_498_);
                                v___x_502_ = l_String_Slice_Pos_get_x3f(v___x_501_, v___x_499_);
                                leanh::lean_dec_ref_known(v___x_501_, 3);
                                if leanh::lean_obj_tag(v___x_502_) == 0 {
                                    v___x_503_ = 65;
                                    v___y_493_ = v___x_503_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_val_504_ = leanh::lean_ctor_get(v___x_502_, 0);
                                    leanh::lean_inc(v_val_504_);
                                    leanh::lean_dec_ref_known(v___x_502_, 1);
                                    v___x_505_ = leanh::lean_unbox_uint32(v_val_504_);
                                    leanh::lean_dec(v_val_504_);
                                    v___y_493_ = v___x_505_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_str_488_);
                                return v_relaxed_486_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_str_488_);
                            v___x_506_ = 0;
                            return v___x_506_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_str_488_);
                        leanh::lean_dec(v_pre_487_);
                        v___x_507_ = 0;
                        return v___x_507_;
                    }
                } else {
                    leanh::lean_dec(v_n_485_);
                    v___x_508_ = 0;
                    return v___x_508_;
                }
            }
            1 => {
                if v___y_490_ == 0 {
                    leanh::lean_dec_ref(v_str_488_);
                    return v___y_490_;
                } else {
                    v___x_491_ =
                        l___private_Lean_Elab_AutoBound_0__Lean_Elab_isValidAutoBoundSuffix(
                            v_str_488_,
                        );
                    return v___x_491_;
                }
            }
            2 => {
                v___x_494_ = 97;
                v___x_495_ = lean_uint32_dec_le(v___x_494_, v___y_493_);
                if v___x_495_ == 0 {
                    v___y_490_ = v___x_495_;
                    state = 1;
                    continue;
                } else {
                    v___x_496_ = 122;
                    v___x_497_ = lean_uint32_dec_le(v___y_493_, v___x_496_);
                    v___y_490_ = v___x_497_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_isValidAutoBoundLevelName___boxed(
    mut v_n_509_: *mut leanh::LeanObject,
    mut v_relaxed_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_relaxed_boxed_511_: u8 = 0;
    let mut v_res_512_: u8 = 0;
    let mut v_r_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_511_ = (leanh::lean_unbox(v_relaxed_510_) as u8);
    v_res_512_ = l_Lean_Elab_isValidAutoBoundLevelName(v_n_509_, v_relaxed_boxed_511_);
    v_r_513_ = leanh::lean_box((v_res_512_) as usize);
    return v_r_513_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = leanh::lean_unsigned_to_nat(32);
    v___x_515_ = lean_mk_empty_array_with_capacity(v___x_514_);
    v___x_516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_516_, 0, v___x_515_);
    return v___x_516_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_517_: usize = 0;
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = 5usize;
    v___x_518_ = leanh::lean_unsigned_to_nat(0);
    v___x_519_ = leanh::lean_unsigned_to_nat(32);
    v___x_520_ = lean_mk_empty_array_with_capacity(v___x_519_);
    v___x_521_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0_once
        ),
        _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__0,
    );
    v___x_522_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_522_, 0, v___x_521_);
    leanh::lean_ctor_set(v___x_522_, 1, v___x_520_);
    leanh::lean_ctor_set(v___x_522_, 2, v___x_518_);
    leanh::lean_ctor_set(v___x_522_, 3, v___x_518_);
    leanh::lean_ctor_set_usize(v___x_522_, 4, v___x_517_);
    return v___x_522_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: u8 = 0;
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_523_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1_once
        ),
        _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__1,
    );
    v___x_524_ = 0;
    v___x_525_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_525_, 0, v___x_523_);
    leanh::lean_ctor_set_uint8(
        v___x_525_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_524_,
    );
    return v___x_525_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default()
-> *mut leanh::LeanObject {
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_526_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2_once
        ),
        _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2,
    );
    return v___x_526_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext()
-> *mut leanh::LeanObject {
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default;
    return v___x_527_;
}
pub unsafe fn _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext()
-> *mut leanh::LeanObject {
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = leanh::lean_unsigned_to_nat(32);
    v___x_529_ = lean_mk_empty_array_with_capacity(v___x_528_);
    leanh::lean_dec_ref(v___x_529_);
    v___x_530_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2_once
        ),
        _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default___closed__2,
    );
    return v___x_530_;
}
pub unsafe fn l_Lean_Elab_AutoBoundImplicitContext_push(
    mut v_ctx_531_: *mut leanh::LeanObject,
    mut v_x_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_autoImplicitEnabled_533_: u8 = 0;
    let mut v_boundVariables_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_537_: u8 = 0;
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_autoImplicitEnabled_533_ = leanh::lean_ctor_get_uint8(
                    v_ctx_531_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_boundVariables_534_ = leanh::lean_ctor_get(v_ctx_531_, 0);
                v_isSharedCheck_542_ = (!leanh::lean_is_exclusive(v_ctx_531_)) as u8;
                if v_isSharedCheck_542_ == 0 {
                    v___x_536_ = v_ctx_531_;
                    v_isShared_537_ = v_isSharedCheck_542_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_boundVariables_534_);
                    leanh::lean_dec(v_ctx_531_);
                    v___x_536_ = leanh::lean_box(0);
                    v_isShared_537_ = v_isSharedCheck_542_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_538_ = l_Lean_PersistentArray_push___redArg(v_boundVariables_534_, v_x_532_);
                if v_isShared_537_ == 0 {
                    leanh::lean_ctor_set(v___x_536_, 0, v___x_538_);
                    v___x_540_ = v___x_536_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_541_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_541_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_autoImplicitEnabled_533_,
                    );
                    v___x_540_ = v_reuseFailAlloc_541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_540_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_AutoBound(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Hint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_366037992____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_autoImplicit = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_autoImplicit);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AutoBound_0__Lean_Elab_initFn_00___x40_Lean_Elab_AutoBound_323533819____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_relaxedAutoImplicit = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_relaxedAutoImplicit);
    leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default =
        _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedAutoBoundImplicitContext_default);
    l_Lean_Elab_instInhabitedAutoBoundImplicitContext =
        _init_l_Lean_Elab_instInhabitedAutoBoundImplicitContext();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedAutoBoundImplicitContext);
    l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext =
        _init_l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext();
    leanh::lean_mark_persistent(l_Lean_Elab_instEmptyCollectionAutoBoundImplicitContext);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_AutoBound(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_AutoBound(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Hint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AutoBound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_AutoBound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_AutoBound(builtin);
}