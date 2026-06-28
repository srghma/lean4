// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Options
// Imports: Lean.Data.Options
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, lean_register_option, runtime_initialize_Lean_Data_Options,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_tag, lean_unbox,
};
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 120, 83, 116, 101, 112, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6359444128274620733 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanStringObject<102> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 102, m_capacity: 102, m_length: 99, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 116, 111, 32, 118, 105, 115, 105, 116, 44, 32, 97, 102, 116, 101, 114, 32, 119, 104, 105, 99, 104, 32, 116, 101, 114, 109, 115, 32, 119, 105, 108, 108, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 32, 97, 115, 32, 96, 226, 139, 175, 96, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 5000 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,287758223889467928 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject,13376943202508946845 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value: LeanStringObject<167> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 167, m_capacity: 167, m_length: 166, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 99, 111, 101, 114, 99, 105, 111, 110, 115, 44, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 112, 114, 111, 111, 102, 32, 116, 101, 114, 109, 115, 44, 32, 102, 117, 108, 108, 121, 32, 113, 117, 97, 108, 105, 102, 105, 101, 100, 32, 110, 97, 109, 101, 115, 44, 32, 117, 110, 105, 118, 101, 114, 115, 101, 44, 32, 97, 110, 100, 32, 100, 105, 115, 97, 98, 108, 101, 32, 98, 101, 116, 97, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 97, 110, 100, 32, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32, 100, 117, 114, 105, 110, 103, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 105, 110, 103, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject,7316224718572721208 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject,1761274844189095662 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value: LeanStringObject<99> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 99, m_capacity: 99, m_length: 98, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 97, 98, 108, 101, 47, 101, 110, 97, 98, 108, 101, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 40, 105, 110, 102, 105, 120, 44, 32, 109, 105, 120, 102, 105, 120, 44, 32, 112, 111, 115, 116, 102, 105, 120, 32, 111, 112, 101, 114, 97, 116, 111, 114, 115, 32, 97, 110, 100, 32, 117, 110, 105, 99, 111, 100, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 41, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject,2931634012575272467 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 97, 114, 101, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject,2877043374944520112 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value: LeanStringObject<93> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 115, 101, 116, 32, 116, 111, 32, 116, 114, 117, 101, 44, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 105, 115, 32, 119, 114, 97, 112, 112, 101, 100, 32, 105, 110, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 101, 115, 32, 114, 101, 103, 97, 114, 100, 108, 101, 115, 115, 32, 111, 102, 32, 112, 114, 101, 99, 101, 100, 101, 110, 99, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject,12192953786141890261 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [117, 110, 105, 99, 111, 100, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject,10942866024302884006 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value: LeanStringObject<82> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 115, 101, 116, 32, 116, 111, 32, 102, 97, 108, 115, 101, 44, 32, 97, 118, 111, 105, 100, 32, 117, 115, 105, 110, 103, 32, 110, 111, 110, 45, 117, 110, 105, 99, 111, 100, 101, 32, 115, 121, 109, 98, 111, 108, 115, 32, 119, 104, 101, 110, 32, 102, 111, 114, 109, 97, 116, 116, 105, 110, 103, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject,17557767932500220843 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject,10942866024302884006 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject,14917885594644788632 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 71, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 115, 101, 116, 32, 116, 111, 32, 116, 114, 117, 101, 44, 32, 117, 115, 101, 32, 117, 110, 105, 99, 111, 100, 101, 32, 96, 226, 134, 166, 96, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 102, 111, 114, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4__value) as *mut LeanObject,17557767932500220843 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject,3065339736393193945 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject,13073215252233618019 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 97, 98, 108, 101, 47, 101, 110, 97, 98, 108, 101, 32, 39, 109, 97, 116, 99, 104, 39, 32, 110, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject,7010021220110325918 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 111, 114, 114, 121, 83, 111, 117, 114, 99, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject,10768827237332984402 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value: LeanStringObject<98> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 98, m_capacity: 98, m_length: 97, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 116, 114, 117, 101, 44, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 32, 39, 115, 111, 114, 114, 121, 39, 32, 119, 105, 116, 104, 32, 105, 116, 115, 32, 111, 114, 105, 103, 105, 110, 97, 116, 105, 110, 103, 32, 115, 111, 117, 114, 99, 101, 32, 112, 111, 115, 105, 116, 105, 111, 110, 44, 32, 105, 102, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject,340588051363606871 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 111, 101, 114, 99, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject,201670708746627072 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 104, 105, 100, 101, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject,13618582251565640709 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject,201670708746627072 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject,5828331324147307825 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 119, 105, 116, 104, 32, 97, 32, 116, 121, 112, 101, 32, 97, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4__value) as *mut LeanObject,13618582251565640709 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject,10121549132578386248 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 110, 105, 118, 101, 114, 115, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject,8756395180368081231 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 117, 110, 105, 118, 101, 114, 115, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject,8087509045201119114 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 117, 108, 108, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject,2239000758558268698 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 102, 117, 108, 108, 121, 32, 113, 117, 97, 108, 105, 102, 105, 101, 100, 32, 110, 97, 109, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject,1369420535650754879 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [112, 114, 105, 118, 97, 116, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject,17722410044048228744 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value: LeanStringObject<73> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 73, m_capacity: 73, m_length: 72, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 110, 97, 109, 101, 115, 32, 97, 115, 115, 105, 103, 110, 101, 100, 32, 116, 111, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject,15532505427886497869 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [102, 117, 110, 66, 105, 110, 100, 101, 114, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject,2971655116940197131 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 108, 97, 109, 98, 100, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject,13358877487021364038 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 105, 66, 105, 110, 100, 101, 114, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject,9961045885826799895 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 112, 105, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject,6290662234070824210 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 105, 66, 105, 110, 100, 101, 114, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject,18111603757228106061 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value: LeanStringObject<168> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 168, m_capacity: 168, m_length: 167, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 110, 97, 109, 101, 115, 32, 102, 111, 114, 32, 112, 105, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 101, 118, 101, 110, 32, 105, 102, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 117, 110, 117, 115, 101, 100, 59, 32, 119, 104, 101, 110, 32, 96, 112, 112, 46, 112, 105, 66, 105, 110, 100, 101, 114, 78, 97, 109, 101, 115, 46, 104, 121, 103, 105, 101, 110, 105, 99, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 32, 116, 104, 101, 110, 32, 117, 110, 117, 115, 101, 100, 32, 104, 121, 103, 105, 101, 110, 105, 99, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 100, 105, 115, 112, 108, 97, 121, 101, 100, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject,11285512238517037704 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject,18111603757228106061 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject,1663457140567834332 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value: LeanStringObject<99> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 99, m_capacity: 99, m_length: 98, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 102, 97, 108, 115, 101, 44, 32, 100, 105, 115, 97, 98, 108, 101, 115, 32, 100, 105, 115, 112, 108, 97, 121, 105, 110, 103, 32, 110, 97, 109, 101, 115, 32, 102, 111, 114, 32, 117, 110, 117, 115, 101, 100, 32, 112, 105, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 119, 105, 116, 104, 32, 104, 121, 103, 105, 101, 110, 105, 99, 32, 110, 97, 109, 101, 115, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4__value) as *mut LeanObject,11285512238517037704 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject,13761443864443915869 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 111, 114, 97, 108, 108, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject,2478016681106523524 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value: LeanStringObject<111> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 108, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 112, 105, 32, 116, 121, 112, 101, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 115, 32, 117, 115, 105, 110, 103, 32, 96, 226, 136, 128, 96, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 32, 119, 105, 116, 104, 32, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 97, 114, 114, 111, 119, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject,12657912554045401513 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 86, 97, 114, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject,16979197608505834392 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 108, 101, 116, 45, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject,16559525104644579261 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 76, 105, 116, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject,10642339427001682784 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 114, 97, 119, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 32, 108, 105, 116, 101, 114, 97, 108, 115, 32, 119, 105, 116, 104, 32, 96, 110, 97, 116, 95, 108, 105, 116, 96, 32, 112, 114, 101, 102, 105, 120, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject,16023585208124697893 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 117, 109, 101, 114, 105, 99, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject,8817743623857380813 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 110, 117, 109, 101, 114, 105, 99, 32, 108, 105, 116, 101, 114, 97, 108, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject,10791999377809290248 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 100, 97, 116, 97, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject,15550957971121913489 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value: LeanStringObject<64> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 115, 32, 97, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 109, 100, 97, 116, 97, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject,13736381634252541804 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 77, 86, 97, 114, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject,16880101017905244153 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 109, 118, 97, 114, 115, 32, 98, 101, 102, 111, 114, 101, 32, 100, 101, 108, 97, 98, 111, 114, 97, 116, 105, 110, 103, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject,17452168760446103860 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 118, 97, 114, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,3547819679331704881 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value: LeanStringObject<171> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 171, m_capacity: 171, m_length: 170, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 110, 97, 109, 101, 115, 32, 111, 102, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 119, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 97, 110, 100, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 101, 109, 32, 97, 115, 32, 39, 63, 95, 39, 32, 40, 102, 111, 114, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 41, 32, 97, 110, 100, 32, 97, 115, 32, 39, 95, 39, 32, 40, 102, 111, 114, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 41, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,370071968865240012 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 101, 118, 101, 108, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,3547819679331704881 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject,6878658951217691401 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value: LeanStringObject<193> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 193, m_capacity: 193, m_length: 192, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 97, 115, 32, 96, 63, 117, 46, 50, 50, 96, 32, 119, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 97, 110, 100, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 101, 109, 32, 97, 115, 32, 39, 95, 39, 46, 32, 87, 104, 101, 110, 32, 101, 105, 116, 104, 101, 114, 32, 39, 112, 112, 46, 109, 118, 97, 114, 115, 39, 32, 111, 114, 32, 39, 112, 112, 46, 109, 118, 97, 114, 115, 46, 97, 110, 111, 110, 121, 109, 111, 117, 115, 39, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 116, 104, 105, 115, 32, 105, 115, 32, 39, 102, 97, 108, 115, 101, 39, 32, 97, 115, 32, 119, 101, 108, 108, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,370071968865240012 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject,16132958297394168888 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,3547819679331704881 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject,8782896581943871241 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value: LeanStringObject<255> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 255, m_capacity: 255, m_length: 254, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 110, 97, 109, 101, 115, 32, 102, 111, 114, 32, 97, 117, 116, 111, 45, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 63, 109, 46, 50, 50, 96, 32, 119, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 97, 110, 100, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 101, 109, 32, 97, 115, 32, 39, 63, 95, 39, 32, 40, 102, 111, 114, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 41, 32, 97, 110, 100, 32, 97, 115, 32, 39, 95, 39, 32, 40, 102, 111, 114, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 41, 46, 32, 87, 104, 101, 110, 32, 39, 112, 112, 46, 109, 118, 97, 114, 115, 39, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 116, 104, 105, 115, 32, 105, 115, 32, 39, 102, 97, 108, 115, 101, 39, 32, 97, 115, 32, 119, 101, 108, 108, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,370071968865240012 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject,17102914560304189496 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [119, 105, 116, 104, 84, 121, 112, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,3547819679331704881 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject,16102878718572707894 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 119, 105, 116, 104, 32, 97, 32, 116, 121, 112, 101, 32, 97, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,370071968865240012 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject,7498389153511150943 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 108, 97, 121, 101, 100, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,3547819679331704881 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject,9486803381567642001 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value: LeanStringObject<111> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 110, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 101, 100, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 119, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 100, 105, 115, 112, 108, 97, 121, 32, 119, 104, 97, 116, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 97, 115, 115, 105, 103, 110, 101, 100, 32, 116, 111, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4__value) as *mut LeanObject,370071968865240012 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject,8059638078715506096 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 118, 97, 114, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject,4690603007435893719 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject,14337813057283747583 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value: LeanStringObject<202> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 202, m_capacity: 202, m_length: 201, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 110, 97, 109, 101, 115, 32, 102, 111, 114, 32, 108, 111, 111, 115, 101, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 40, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 41, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 95, 102, 118, 97, 114, 46, 50, 50, 96, 32, 119, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 97, 110, 100, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 101, 109, 32, 97, 115, 32, 96, 95, 102, 118, 97, 114, 46, 95, 96, 46, 32, 85, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 115, 116, 97, 98, 105, 108, 105, 122, 105, 110, 103, 32, 111, 117, 116, 112, 117, 116, 32, 105, 110, 32, 96, 35, 103, 117, 97, 114, 100, 95, 109, 115, 103, 115, 96, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject,17924765772004779986 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4__value) as *mut LeanObject,14986572428227958718 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 101, 116, 97, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject,4208268519823556226 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value: LeanStringObject<59> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 97, 112, 112, 108, 121, 32, 98, 101, 116, 97, 45, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 119, 104, 101, 110, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 105, 110, 103, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject,5294471269784423847 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 101, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,12369823485913714957 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value: LeanStringObject<212> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 212, m_capacity: 212, m_length: 207, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 39, 123, 32, 102, 105, 101, 108, 100, 78, 97, 109, 101, 32, 58, 61, 32, 102, 105, 101, 108, 100, 86, 97, 108, 117, 101, 44, 32, 46, 46, 46, 32, 125, 39, 32, 110, 111, 116, 97, 116, 105, 111, 110, 44, 32, 111, 114, 32, 117, 115, 105, 110, 103, 32, 39, 226, 159, 168, 102, 105, 101, 108, 100, 86, 97, 108, 117, 101, 44, 32, 46, 46, 46, 32, 226, 159, 169, 39, 32, 105, 102, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 115, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 39, 64, 91, 112, 112, 95, 117, 115, 105, 110, 103, 95, 97, 110, 111, 110, 121, 109, 111, 117, 115, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 93, 39, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,5858607989623052872 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 108, 97, 116, 116, 101, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,12369823485913714957 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject,7548337011162420373 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 102, 108, 97, 116, 116, 101, 110, 32, 110, 101, 115, 116, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 102, 111, 114, 32, 112, 97, 114, 101, 110, 116, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,5858607989623052872 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject,16708430544847064980 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 101, 102, 97, 117, 108, 116, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,12369823485913714957 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject,6857859621529531492 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value: LeanStringObject<90> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 102, 97, 108, 115, 101, 44, 32, 111, 109, 105, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 102, 105, 101, 108, 100, 115, 32, 116, 104, 97, 116, 32, 101, 113, 117, 97, 108, 32, 116, 104, 101, 105, 114, 32, 100, 101, 102, 97, 117, 108, 116, 32, 118, 97, 108, 117, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4__value) as *mut LeanObject,5858607989623052872 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject,10316334255685226341 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [102, 105, 101, 108, 100, 78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject,5934246346384427136 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value: LeanStringObject<127> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 127, m_capacity: 127, m_length: 126, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 117, 115, 101, 32, 102, 105, 101, 108, 100, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 119, 104, 101, 110, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 105, 110, 103, 44, 32, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 102, 111, 114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 44, 32, 117, 110, 108, 101, 115, 115, 32, 39, 64, 91, 112, 112, 95, 110, 111, 100, 111, 116, 93, 39, 32, 105, 115, 32, 97, 112, 112, 108, 105, 101, 100, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject,156480323903410053 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 100, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject,5934246346384427136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject,8807860425742352464 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 119, 104, 101, 110, 32, 96, 112, 112, 46, 102, 105, 101, 108, 100, 78, 111, 116, 97, 116, 105, 111, 110, 96, 32, 105, 115, 32, 116, 114, 117, 101, 44, 32, 101, 110, 97, 98, 108, 101, 32, 117, 115, 105, 110, 103, 32, 103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 100, 32, 102, 105, 101, 108, 100, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 119, 104, 101, 110, 32, 116, 104, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 102, 105, 101, 108, 100, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 105, 115, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 101, 120, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4__value) as *mut LeanObject,156480323903410053 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject,5443888657244857657 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject,18006822408276635015 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject,3400081749016339490 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 101, 73, 110, 115, 116, 97, 110, 99, 101, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject,13675844337944598589 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 121, 112, 101, 32, 111, 102, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject,11336434452729686296 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 97, 102, 101, 83, 104, 97, 100, 111, 119, 105, 110, 103, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject,4786914124816531163 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 97, 108, 108, 111, 119, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 115, 104, 97, 100, 111, 119, 105, 110, 103, 32, 105, 102, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 110, 111, 32, 99, 111, 108, 108, 105, 115, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject,14616630247551284598 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 103, 65, 112, 112, 70, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject,11389724230315925419 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value: LeanStringObject<83> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 116, 97, 103, 32, 97, 108, 108, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 116, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 110, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject,7992134874597290150 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 114, 111, 111, 102, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,2303122768139892240 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value: LeanStringObject<111> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 108, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 112, 114, 111, 111, 102, 115, 32, 119, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 97, 110, 100, 32, 114, 101, 112, 108, 97, 99, 101, 32, 112, 114, 111, 111, 102, 115, 32, 97, 112, 112, 101, 97, 114, 105, 110, 103, 32, 119, 105, 116, 104, 105, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 98, 121, 32, 96, 226, 139, 175, 96, 32, 119, 104, 101, 110, 32, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,13305467326265152117 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,2303122768139892240 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject,4659511660905808491 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value: LeanStringObject<88> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 87, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 119, 104, 101, 110, 32, 96, 112, 112, 46, 112, 114, 111, 111, 102, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 97, 100, 100, 115, 32, 97, 32, 116, 121, 112, 101, 32, 97, 115, 99, 114, 105, 112, 116, 105, 111, 110, 32, 116, 111, 32, 116, 104, 101, 32, 111, 109, 105, 116, 116, 101, 100, 32, 112, 114, 111, 111, 102, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,13305467326265152117 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4__value) as *mut LeanObject,14643533762120912546 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,2303122768139892240 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject,5436582824390922172 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value: LeanStringObject<124> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 124, m_capacity: 124, m_length: 121, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 119, 104, 101, 110, 32, 96, 112, 112, 46, 112, 114, 111, 111, 102, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 99, 111, 110, 116, 114, 111, 108, 115, 32, 116, 104, 101, 32, 99, 111, 109, 112, 108, 101, 120, 105, 116, 121, 32, 111, 102, 32, 112, 114, 111, 111, 102, 115, 32, 97, 116, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 121, 32, 98, 101, 103, 105, 110, 32, 98, 101, 105, 110, 103, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 96, 226, 139, 175, 96, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4__value) as *mut LeanObject,13305467326265152117 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject,14786224574633415773 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject,3793822569425731127 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value: LeanStringObject<109> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 109, m_capacity: 109, m_length: 108, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 105, 102, 32, 115, 101, 116, 32, 116, 111, 32, 102, 97, 108, 115, 101, 44, 32, 114, 101, 112, 108, 97, 99, 101, 32, 105, 110, 115, 116, 45, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 116, 111, 32, 101, 120, 112, 108, 105, 99, 105, 116, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 119, 105, 116, 104, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject,11312082511887892338 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject,18355807383429720985 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value: LeanStringObject<96> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 119, 104, 101, 110, 32, 112, 114, 105, 110, 116, 105, 110, 103, 32, 101, 120, 112, 108, 105, 99, 105, 116, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 44, 32, 115, 104, 111, 119, 32, 116, 104, 101, 32, 116, 121, 112, 101, 115, 32, 111, 102, 32, 105, 110, 115, 116, 45, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject,8587934613882580884 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 101, 101, 112, 84, 101, 114, 109, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject,11437646603995311168 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value: LeanStringObject<88> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 85, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 100, 105, 115, 112, 108, 97, 121, 32, 100, 101, 101, 112, 108, 121, 32, 110, 101, 115, 116, 101, 100, 32, 116, 101, 114, 109, 115, 44, 32, 114, 101, 112, 108, 97, 99, 105, 110, 103, 32, 116, 104, 101, 109, 32, 119, 105, 116, 104, 32, 96, 226, 139, 175, 96, 32, 105, 102, 32, 115, 101, 116, 32, 116, 111, 32, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject,11467941592979173445 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject,11437646603995311168 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject,2572497286751565260 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value: LeanStringObject<104> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 101, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 119, 104, 101, 110, 32, 96, 112, 112, 46, 100, 101, 101, 112, 84, 101, 114, 109, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 116, 104, 101, 32, 100, 101, 112, 116, 104, 32, 97, 116, 32, 119, 104, 105, 99, 104, 32, 116, 101, 114, 109, 115, 32, 115, 116, 97, 114, 116, 32, 98, 101, 105, 110, 103, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 96, 226, 139, 175, 96, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4__value) as *mut LeanObject,11467941592979173445 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4__value) as *mut LeanObject,5678128505579160845 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 111, 116, 105, 118, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 105, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,16853493998702655092 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,11991880496408799537 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 105, 110, 116, 32, 97, 108, 108, 32, 109, 111, 116, 105, 118, 101, 115, 32, 116, 104, 97, 116, 32, 114, 101, 116, 117, 114, 110, 32, 112, 105, 32, 116, 121, 112, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,5463605448360433721 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,11513882900070867936 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 111, 110, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,16853493998702655092 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject,8705094809840200778 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 105, 110, 116, 32, 97, 108, 108, 32, 109, 111, 116, 105, 118, 101, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 110, 111, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,5463605448360433721 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject,589023454224727067 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,16853493998702655092 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject,5172705685851038260 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 105, 110, 116, 32, 97, 108, 108, 32, 109, 111, 116, 105, 118, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4__value) as *mut LeanObject,5463605448360433721 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__value) as *mut LeanObject,15649939633956023005 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4__value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__spec__0(
    mut v_name_1761_: *mut LeanObject,
    mut v_decl_1762_: *mut LeanObject,
    mut v_ref_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut v_unused_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1765_ = lean_ctor_get(v_decl_1762_, 0);
                v_descr_1766_ = lean_ctor_get(v_decl_1762_, 1);
                v_deprecation_x3f_1767_ = lean_ctor_get(v_decl_1762_, 2);
                lean_inc(v_defValue_1765_);
                v___x_1768_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1768_, 0, v_defValue_1765_);
                lean_inc(v_deprecation_x3f_1767_);
                lean_inc_ref(v_descr_1766_);
                lean_inc_n(v_name_1761_, 2);
                v___x_1769_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1769_, 0, v_name_1761_);
                lean_ctor_set(v___x_1769_, 1, v_ref_1763_);
                lean_ctor_set(v___x_1769_, 2, v___x_1768_);
                lean_ctor_set(v___x_1769_, 3, v_descr_1766_);
                lean_ctor_set(v___x_1769_, 4, v_deprecation_x3f_1767_);
                v___x_1770_ = lean_register_option(v_name_1761_, v___x_1769_);
                if lean_obj_tag(v___x_1770_) == 0 {
                    v_isSharedCheck_1778_ = (!lean_is_exclusive(v___x_1770_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v_unused_1779_ = lean_ctor_get(v___x_1770_, 0);
                        lean_dec(v_unused_1779_);
                        v___x_1772_ = v___x_1770_;
                        v_isShared_1773_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1770_);
                        v___x_1772_ = lean_box(0);
                        v_isShared_1773_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1761_);
                    v_a_1780_ = lean_ctor_get(v___x_1770_, 0);
                    v_isSharedCheck_1787_ = (!lean_is_exclusive(v___x_1770_)) as u8;
                    if v_isSharedCheck_1787_ == 0 {
                        v___x_1782_ = v___x_1770_;
                        v_isShared_1783_ = v_isSharedCheck_1787_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1780_);
                        lean_dec(v___x_1770_);
                        v___x_1782_ = lean_box(0);
                        v_isShared_1783_ = v_isSharedCheck_1787_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1765_);
                v___x_1774_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1774_, 0, v_name_1761_);
                lean_ctor_set(v___x_1774_, 1, v_defValue_1765_);
                if v_isShared_1773_ == 0 {
                    lean_ctor_set(v___x_1772_, 0, v___x_1774_);
                    v___x_1776_ = v___x_1772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
                    v___x_1776_ = v_reuseFailAlloc_1777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1776_;
            }
            3 => {
                if v_isShared_1783_ == 0 {
                    v___x_1785_ = v___x_1782_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
                    v___x_1785_ = v_reuseFailAlloc_1786_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1788_: *mut LeanObject,
    mut v_decl_1789_: *mut LeanObject,
    mut v_ref_1790_: *mut LeanObject,
    mut v_a_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1792_: *mut LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__spec__0(v_name_1788_, v_decl_1789_, v_ref_1790_);
    lean_dec_ref(v_decl_1789_);
    return v_res_1792_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    v___x_1809_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_;
    v___x_1810_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_;
    v___x_1811_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_;
    v___x_1812_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__spec__0(v___x_1809_, v___x_1810_, v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4____boxed(
    mut v_a_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1814_: *mut LeanObject = core::ptr::null_mut();
    v_res_1814_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_();
    return v_res_1814_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(
    mut v_name_1815_: *mut LeanObject,
    mut v_decl_1816_: *mut LeanObject,
    mut v_ref_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut v_unused_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1819_ = lean_ctor_get(v_decl_1816_, 0);
                v_descr_1820_ = lean_ctor_get(v_decl_1816_, 1);
                v_deprecation_x3f_1821_ = lean_ctor_get(v_decl_1816_, 2);
                v___x_1822_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1823_ = (lean_unbox(v_defValue_1819_) as u8);
                lean_ctor_set_uint8(v___x_1822_, 0 as u32, v___x_1823_);
                lean_inc(v_deprecation_x3f_1821_);
                lean_inc_ref(v_descr_1820_);
                lean_inc_n(v_name_1815_, 2);
                v___x_1824_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1824_, 0, v_name_1815_);
                lean_ctor_set(v___x_1824_, 1, v_ref_1817_);
                lean_ctor_set(v___x_1824_, 2, v___x_1822_);
                lean_ctor_set(v___x_1824_, 3, v_descr_1820_);
                lean_ctor_set(v___x_1824_, 4, v_deprecation_x3f_1821_);
                v___x_1825_ = lean_register_option(v_name_1815_, v___x_1824_);
                if lean_obj_tag(v___x_1825_) == 0 {
                    v_isSharedCheck_1833_ = (!lean_is_exclusive(v___x_1825_)) as u8;
                    if v_isSharedCheck_1833_ == 0 {
                        v_unused_1834_ = lean_ctor_get(v___x_1825_, 0);
                        lean_dec(v_unused_1834_);
                        v___x_1827_ = v___x_1825_;
                        v_isShared_1828_ = v_isSharedCheck_1833_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1825_);
                        v___x_1827_ = lean_box(0);
                        v_isShared_1828_ = v_isSharedCheck_1833_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1815_);
                    v_a_1835_ = lean_ctor_get(v___x_1825_, 0);
                    v_isSharedCheck_1842_ = (!lean_is_exclusive(v___x_1825_)) as u8;
                    if v_isSharedCheck_1842_ == 0 {
                        v___x_1837_ = v___x_1825_;
                        v_isShared_1838_ = v_isSharedCheck_1842_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1835_);
                        lean_dec(v___x_1825_);
                        v___x_1837_ = lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1842_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1819_);
                v___x_1829_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1829_, 0, v_name_1815_);
                lean_ctor_set(v___x_1829_, 1, v_defValue_1819_);
                if v_isShared_1828_ == 0 {
                    lean_ctor_set(v___x_1827_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                    v___x_1831_ = v_reuseFailAlloc_1832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1831_;
            }
            3 => {
                if v_isShared_1838_ == 0 {
                    v___x_1840_ = v___x_1837_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
                    v___x_1840_ = v_reuseFailAlloc_1841_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1843_: *mut LeanObject,
    mut v_decl_1844_: *mut LeanObject,
    mut v_ref_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v_name_1843_, v_decl_1844_, v_ref_1845_);
    lean_dec_ref(v_decl_1844_);
    return v_res_1847_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1863_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_;
    v___x_1864_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_;
    v___x_1865_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_;
    v___x_1866_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1863_, v___x_1864_, v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4____boxed(
    mut v_a_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1868_: *mut LeanObject = core::ptr::null_mut();
    v_res_1868_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_();
    return v_res_1868_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    v___x_1884_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_;
    v___x_1885_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_;
    v___x_1886_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_;
    v___x_1887_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1884_, v___x_1885_, v___x_1886_);
    return v___x_1887_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4____boxed(
    mut v_a_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1889_: *mut LeanObject = core::ptr::null_mut();
    v_res_1889_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_();
    return v_res_1889_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_;
    v___x_1906_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_;
    v___x_1907_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_;
    v___x_1908_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1905_, v___x_1906_, v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4____boxed(
    mut v_a_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1910_: *mut LeanObject = core::ptr::null_mut();
    v_res_1910_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_();
    return v_res_1910_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1926_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_;
    v___x_1927_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_;
    v___x_1928_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_;
    v___x_1929_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1926_, v___x_1927_, v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4____boxed(
    mut v_a_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1931_: *mut LeanObject = core::ptr::null_mut();
    v_res_1931_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_();
    return v_res_1931_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    v___x_1949_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_;
    v___x_1950_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_;
    v___x_1951_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_;
    v___x_1952_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1949_, v___x_1950_, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4____boxed(
    mut v_a_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1954_: *mut LeanObject = core::ptr::null_mut();
    v_res_1954_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_();
    return v_res_1954_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_;
    v___x_1971_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_;
    v___x_1972_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_;
    v___x_1973_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1970_, v___x_1971_, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4____boxed(
    mut v_a_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_();
    return v_res_1975_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    v___x_1991_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_;
    v___x_1992_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_;
    v___x_1993_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_;
    v___x_1994_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_1991_, v___x_1992_, v___x_1993_);
    return v___x_1994_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4____boxed(
    mut v_a_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1996_: *mut LeanObject = core::ptr::null_mut();
    v_res_1996_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_();
    return v_res_1996_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_;
    v___x_2013_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_;
    v___x_2014_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_;
    v___x_2015_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2012_, v___x_2013_, v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4____boxed(
    mut v_a_2016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2017_: *mut LeanObject = core::ptr::null_mut();
    v_res_2017_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_();
    return v_res_2017_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    v___x_2035_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_;
    v___x_2036_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_;
    v___x_2037_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_;
    v___x_2038_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2035_, v___x_2036_, v___x_2037_);
    return v___x_2038_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4____boxed(
    mut v_a_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2040_: *mut LeanObject = core::ptr::null_mut();
    v_res_2040_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_();
    return v_res_2040_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    v___x_2056_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_;
    v___x_2057_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_;
    v___x_2058_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_;
    v___x_2059_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2056_, v___x_2057_, v___x_2058_);
    return v___x_2059_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4____boxed(
    mut v_a_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2061_: *mut LeanObject = core::ptr::null_mut();
    v_res_2061_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_();
    return v_res_2061_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    v___x_2077_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_;
    v___x_2078_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_;
    v___x_2079_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_;
    v___x_2080_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2077_, v___x_2078_, v___x_2079_);
    return v___x_2080_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4____boxed(
    mut v_a_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2082_: *mut LeanObject = core::ptr::null_mut();
    v_res_2082_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_();
    return v_res_2082_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    v___x_2098_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_;
    v___x_2099_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_;
    v___x_2100_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_;
    v___x_2101_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2098_, v___x_2099_, v___x_2100_);
    return v___x_2101_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4____boxed(
    mut v_a_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2103_: *mut LeanObject = core::ptr::null_mut();
    v_res_2103_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_();
    return v_res_2103_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2119_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_;
    v___x_2120_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_;
    v___x_2121_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_;
    v___x_2122_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2119_, v___x_2120_, v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4____boxed(
    mut v_a_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2124_: *mut LeanObject = core::ptr::null_mut();
    v_res_2124_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_();
    return v_res_2124_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v___x_2140_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_;
    v___x_2141_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_;
    v___x_2142_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_;
    v___x_2143_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2140_, v___x_2141_, v___x_2142_);
    return v___x_2143_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4____boxed(
    mut v_a_2144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2145_: *mut LeanObject = core::ptr::null_mut();
    v_res_2145_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_();
    return v_res_2145_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    v___x_2161_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_;
    v___x_2162_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_;
    v___x_2163_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_;
    v___x_2164_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2161_, v___x_2162_, v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4____boxed(
    mut v_a_2165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2166_: *mut LeanObject = core::ptr::null_mut();
    v_res_2166_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_();
    return v_res_2166_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    v___x_2184_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_;
    v___x_2185_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_;
    v___x_2186_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_;
    v___x_2187_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2184_, v___x_2185_, v___x_2186_);
    return v___x_2187_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4____boxed(
    mut v_a_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2189_: *mut LeanObject = core::ptr::null_mut();
    v_res_2189_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_();
    return v_res_2189_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_;
    v___x_2206_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_;
    v___x_2207_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_;
    v___x_2208_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2205_, v___x_2206_, v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4____boxed(
    mut v_a_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_();
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    v___x_2226_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_;
    v___x_2227_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_;
    v___x_2228_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_;
    v___x_2229_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2226_, v___x_2227_, v___x_2228_);
    return v___x_2229_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4____boxed(
    mut v_a_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_();
    return v_res_2231_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2247_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_;
    v___x_2248_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_;
    v___x_2249_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_;
    v___x_2250_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2247_, v___x_2248_, v___x_2249_);
    return v___x_2250_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4____boxed(
    mut v_a_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2252_: *mut LeanObject = core::ptr::null_mut();
    v_res_2252_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_();
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    v___x_2268_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_;
    v___x_2269_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_;
    v___x_2270_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_;
    v___x_2271_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2268_, v___x_2269_, v___x_2270_);
    return v___x_2271_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4____boxed(
    mut v_a_2272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2273_: *mut LeanObject = core::ptr::null_mut();
    v_res_2273_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_();
    return v_res_2273_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    v___x_2289_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_;
    v___x_2290_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_;
    v___x_2291_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_;
    v___x_2292_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2289_, v___x_2290_, v___x_2291_);
    return v___x_2292_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4____boxed(
    mut v_a_2293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2294_: *mut LeanObject = core::ptr::null_mut();
    v_res_2294_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_();
    return v_res_2294_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_;
    v___x_2311_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_;
    v___x_2312_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_;
    v___x_2313_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2310_, v___x_2311_, v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4____boxed(
    mut v_a_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_();
    return v_res_2315_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    v___x_2331_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_;
    v___x_2332_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_;
    v___x_2333_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_;
    v___x_2334_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2331_, v___x_2332_, v___x_2333_);
    return v___x_2334_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4____boxed(
    mut v_a_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2336_: *mut LeanObject = core::ptr::null_mut();
    v_res_2336_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_();
    return v_res_2336_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2354_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_;
    v___x_2355_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_;
    v___x_2356_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_;
    v___x_2357_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2354_, v___x_2355_, v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4____boxed(
    mut v_a_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2359_: *mut LeanObject = core::ptr::null_mut();
    v_res_2359_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_();
    return v_res_2359_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___x_2377_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_;
    v___x_2378_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_;
    v___x_2379_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_;
    v___x_2380_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2377_, v___x_2378_, v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4____boxed(
    mut v_a_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2382_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_();
    return v_res_2382_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    v___x_2400_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_;
    v___x_2401_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_;
    v___x_2402_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_;
    v___x_2403_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2400_, v___x_2401_, v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4____boxed(
    mut v_a_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2405_: *mut LeanObject = core::ptr::null_mut();
    v_res_2405_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_();
    return v_res_2405_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    v___x_2423_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_;
    v___x_2424_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_;
    v___x_2425_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_;
    v___x_2426_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2423_, v___x_2424_, v___x_2425_);
    return v___x_2426_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4____boxed(
    mut v_a_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2428_: *mut LeanObject = core::ptr::null_mut();
    v_res_2428_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_();
    return v_res_2428_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    v___x_2446_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_;
    v___x_2447_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_;
    v___x_2448_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_;
    v___x_2449_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2446_, v___x_2447_, v___x_2448_);
    return v___x_2449_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4____boxed(
    mut v_a_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2451_: *mut LeanObject = core::ptr::null_mut();
    v_res_2451_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_();
    return v_res_2451_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    v___x_2467_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_;
    v___x_2468_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_;
    v___x_2469_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_;
    v___x_2470_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2467_, v___x_2468_, v___x_2469_);
    return v___x_2470_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4____boxed(
    mut v_a_2471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2472_: *mut LeanObject = core::ptr::null_mut();
    v_res_2472_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_();
    return v_res_2472_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    v___x_2488_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_;
    v___x_2489_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_;
    v___x_2490_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_;
    v___x_2491_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2488_, v___x_2489_, v___x_2490_);
    return v___x_2491_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4____boxed(
    mut v_a_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_();
    return v_res_2493_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    v___x_2511_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_;
    v___x_2512_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_;
    v___x_2513_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_;
    v___x_2514_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2511_, v___x_2512_, v___x_2513_);
    return v___x_2514_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4____boxed(
    mut v_a_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2516_: *mut LeanObject = core::ptr::null_mut();
    v_res_2516_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_();
    return v_res_2516_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    v___x_2534_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_;
    v___x_2535_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_;
    v___x_2536_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_;
    v___x_2537_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2534_, v___x_2535_, v___x_2536_);
    return v___x_2537_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4____boxed(
    mut v_a_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2539_: *mut LeanObject = core::ptr::null_mut();
    v_res_2539_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_();
    return v_res_2539_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    v___x_2555_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_;
    v___x_2556_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_;
    v___x_2557_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_;
    v___x_2558_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2555_, v___x_2556_, v___x_2557_);
    return v___x_2558_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4____boxed(
    mut v_a_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2560_: *mut LeanObject = core::ptr::null_mut();
    v_res_2560_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_();
    return v_res_2560_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_;
    v___x_2579_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_;
    v___x_2580_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_;
    v___x_2581_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2578_, v___x_2579_, v___x_2580_);
    return v___x_2581_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4____boxed(
    mut v_a_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2583_: *mut LeanObject = core::ptr::null_mut();
    v_res_2583_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_();
    return v_res_2583_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    v___x_2599_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_;
    v___x_2600_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_;
    v___x_2601_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_;
    v___x_2602_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2599_, v___x_2600_, v___x_2601_);
    return v___x_2602_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4____boxed(
    mut v_a_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2604_: *mut LeanObject = core::ptr::null_mut();
    v_res_2604_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_();
    return v_res_2604_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    v___x_2620_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_;
    v___x_2621_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_;
    v___x_2622_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_;
    v___x_2623_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2620_, v___x_2621_, v___x_2622_);
    return v___x_2623_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4____boxed(
    mut v_a_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_();
    return v_res_2625_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2641_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_;
    v___x_2642_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_;
    v___x_2643_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_;
    v___x_2644_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2641_, v___x_2642_, v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4____boxed(
    mut v_a_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2646_: *mut LeanObject = core::ptr::null_mut();
    v_res_2646_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_();
    return v_res_2646_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2662_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_;
    v___x_2663_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_;
    v___x_2664_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_;
    v___x_2665_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2662_, v___x_2663_, v___x_2664_);
    return v___x_2665_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4____boxed(
    mut v_a_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2667_: *mut LeanObject = core::ptr::null_mut();
    v_res_2667_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_();
    return v_res_2667_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_;
    v___x_2684_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_;
    v___x_2685_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_;
    v___x_2686_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2683_, v___x_2684_, v___x_2685_);
    return v___x_2686_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4____boxed(
    mut v_a_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2688_: *mut LeanObject = core::ptr::null_mut();
    v_res_2688_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_();
    return v_res_2688_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    v___x_2705_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_;
    v___x_2706_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_;
    v___x_2707_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_;
    v___x_2708_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2705_, v___x_2706_, v___x_2707_);
    return v___x_2708_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4____boxed(
    mut v_a_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2710_: *mut LeanObject = core::ptr::null_mut();
    v_res_2710_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_();
    return v_res_2710_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    v___x_2727_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_;
    v___x_2728_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_;
    v___x_2729_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_;
    v___x_2730_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__spec__0(v___x_2727_, v___x_2728_, v___x_2729_);
    return v___x_2730_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4____boxed(
    mut v_a_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2732_: *mut LeanObject = core::ptr::null_mut();
    v_res_2732_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_();
    return v_res_2732_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_;
    v___x_2749_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_;
    v___x_2750_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_;
    v___x_2751_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2748_, v___x_2749_, v___x_2750_);
    return v___x_2751_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4____boxed(
    mut v_a_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2753_: *mut LeanObject = core::ptr::null_mut();
    v_res_2753_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_();
    return v_res_2753_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    v___x_2769_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_;
    v___x_2770_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_;
    v___x_2771_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_;
    v___x_2772_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2769_, v___x_2770_, v___x_2771_);
    return v___x_2772_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4____boxed(
    mut v_a_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2774_: *mut LeanObject = core::ptr::null_mut();
    v_res_2774_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_();
    return v_res_2774_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    v___x_2790_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_;
    v___x_2791_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_;
    v___x_2792_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_;
    v___x_2793_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2790_, v___x_2791_, v___x_2792_);
    return v___x_2793_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4____boxed(
    mut v_a_2794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2795_: *mut LeanObject = core::ptr::null_mut();
    v_res_2795_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_();
    return v_res_2795_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    v___x_2811_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_;
    v___x_2812_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_;
    v___x_2813_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_;
    v___x_2814_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4__spec__0(v___x_2811_, v___x_2812_, v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4____boxed(
    mut v_a_2815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2816_: *mut LeanObject = core::ptr::null_mut();
    v_res_2816_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_();
    return v_res_2816_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    v___x_2835_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_;
    v___x_2836_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_;
    v___x_2837_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_;
    v___x_2838_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2835_, v___x_2836_, v___x_2837_);
    return v___x_2838_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4____boxed(
    mut v_a_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2840_: *mut LeanObject = core::ptr::null_mut();
    v_res_2840_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_();
    return v_res_2840_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    v___x_2858_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_;
    v___x_2859_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_;
    v___x_2860_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_;
    v___x_2861_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2858_, v___x_2859_, v___x_2860_);
    return v___x_2861_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4____boxed(
    mut v_a_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2863_: *mut LeanObject = core::ptr::null_mut();
    v_res_2863_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_();
    return v_res_2863_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    v___x_2880_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_;
    v___x_2881_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_;
    v___x_2882_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_;
    v___x_2883_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4__spec__0(v___x_2880_, v___x_2881_, v___x_2882_);
    return v___x_2883_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4____boxed(
    mut v_a_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2885_: *mut LeanObject = core::ptr::null_mut();
    v_res_2885_ = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_();
    return v_res_2885_;
}
pub unsafe fn l_Lean_getPPMaxSteps(mut v_o_2886_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    v___x_2887_ = l_Lean_pp_maxSteps;
    v_name_2888_ = lean_ctor_get(v___x_2887_, 0);
    v_defValue_2889_ = lean_ctor_get(v___x_2887_, 1);
    v_map_2890_ = lean_ctor_get(v_o_2886_, 0);
    v___x_2891_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2890_,
            v_name_2888_,
        );
    if lean_obj_tag(v___x_2891_) == 0 {
        lean_inc(v_defValue_2889_);
        return v_defValue_2889_;
    } else {
        let mut v_val_2892_: *mut LeanObject = core::ptr::null_mut();
        v_val_2892_ = lean_ctor_get(v___x_2891_, 0);
        lean_inc(v_val_2892_);
        lean_dec_ref_known(v___x_2891_, 1);
        if lean_obj_tag(v_val_2892_) == 3 {
            let mut v_v_2893_: *mut LeanObject = core::ptr::null_mut();
            v_v_2893_ = lean_ctor_get(v_val_2892_, 0);
            lean_inc(v_v_2893_);
            lean_dec_ref_known(v_val_2892_, 1);
            return v_v_2893_;
        } else {
            lean_dec(v_val_2892_);
            lean_inc(v_defValue_2889_);
            return v_defValue_2889_;
        }
    }
}
pub unsafe fn l_Lean_getPPMaxSteps___boxed(mut v_o_2894_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2895_: *mut LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Lean_getPPMaxSteps(v_o_2894_);
    lean_dec_ref(v_o_2894_);
    return v_res_2895_;
}
pub unsafe fn l_Lean_getPPAll(mut v_o_2896_: *mut LeanObject) -> u8 {
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    v___x_2897_ = l_Lean_pp_all;
    v_name_2898_ = lean_ctor_get(v___x_2897_, 0);
    v_map_2899_ = lean_ctor_get(v_o_2896_, 0);
    v___x_2900_ = 0;
    v___x_2901_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2899_,
            v_name_2898_,
        );
    if lean_obj_tag(v___x_2901_) == 0 {
        return v___x_2900_;
    } else {
        let mut v_val_2902_: *mut LeanObject = core::ptr::null_mut();
        v_val_2902_ = lean_ctor_get(v___x_2901_, 0);
        lean_inc(v_val_2902_);
        lean_dec_ref_known(v___x_2901_, 1);
        if lean_obj_tag(v_val_2902_) == 1 {
            let mut v_v_2903_: u8 = 0;
            v_v_2903_ = lean_ctor_get_uint8(v_val_2902_, 0 as u32);
            lean_dec_ref_known(v_val_2902_, 0);
            return v_v_2903_;
        } else {
            lean_dec(v_val_2902_);
            return v___x_2900_;
        }
    }
}
pub unsafe fn l_Lean_getPPAll___boxed(mut v_o_2904_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2905_: u8 = 0;
    let mut v_r_2906_: *mut LeanObject = core::ptr::null_mut();
    v_res_2905_ = l_Lean_getPPAll(v_o_2904_);
    lean_dec_ref(v_o_2904_);
    v_r_2906_ = lean_box((v_res_2905_) as usize);
    return v_r_2906_;
}
pub unsafe fn l_Lean_getPPFunBinderTypes(mut v_o_2907_: *mut LeanObject) -> u8 {
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    v___x_2908_ = l_Lean_pp_funBinderTypes;
    v_name_2909_ = lean_ctor_get(v___x_2908_, 0);
    v_map_2910_ = lean_ctor_get(v_o_2907_, 0);
    v___x_2911_ = l_Lean_getPPAll(v_o_2907_);
    v___x_2912_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2910_,
            v_name_2909_,
        );
    if lean_obj_tag(v___x_2912_) == 0 {
        return v___x_2911_;
    } else {
        let mut v_val_2913_: *mut LeanObject = core::ptr::null_mut();
        v_val_2913_ = lean_ctor_get(v___x_2912_, 0);
        lean_inc(v_val_2913_);
        lean_dec_ref_known(v___x_2912_, 1);
        if lean_obj_tag(v_val_2913_) == 1 {
            let mut v_v_2914_: u8 = 0;
            v_v_2914_ = lean_ctor_get_uint8(v_val_2913_, 0 as u32);
            lean_dec_ref_known(v_val_2913_, 0);
            return v_v_2914_;
        } else {
            lean_dec(v_val_2913_);
            return v___x_2911_;
        }
    }
}
pub unsafe fn l_Lean_getPPFunBinderTypes___boxed(
    mut v_o_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2916_: u8 = 0;
    let mut v_r_2917_: *mut LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_Lean_getPPFunBinderTypes(v_o_2915_);
    lean_dec_ref(v_o_2915_);
    v_r_2917_ = lean_box((v_res_2916_) as usize);
    return v_r_2917_;
}
pub unsafe fn l_Lean_getPPPiBinderTypes(mut v_o_2918_: *mut LeanObject) -> u8 {
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    v___x_2919_ = l_Lean_pp_piBinderTypes;
    v_name_2920_ = lean_ctor_get(v___x_2919_, 0);
    v_defValue_2921_ = lean_ctor_get(v___x_2919_, 1);
    v_map_2922_ = lean_ctor_get(v_o_2918_, 0);
    v___x_2923_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2922_,
            v_name_2920_,
        );
    if lean_obj_tag(v___x_2923_) == 0 {
        let mut v___x_2924_: u8 = 0;
        v___x_2924_ = (lean_unbox(v_defValue_2921_) as u8);
        return v___x_2924_;
    } else {
        let mut v_val_2925_: *mut LeanObject = core::ptr::null_mut();
        v_val_2925_ = lean_ctor_get(v___x_2923_, 0);
        lean_inc(v_val_2925_);
        lean_dec_ref_known(v___x_2923_, 1);
        if lean_obj_tag(v_val_2925_) == 1 {
            let mut v_v_2926_: u8 = 0;
            v_v_2926_ = lean_ctor_get_uint8(v_val_2925_, 0 as u32);
            lean_dec_ref_known(v_val_2925_, 0);
            return v_v_2926_;
        } else {
            let mut v___x_2927_: u8 = 0;
            lean_dec(v_val_2925_);
            v___x_2927_ = (lean_unbox(v_defValue_2921_) as u8);
            return v___x_2927_;
        }
    }
}
pub unsafe fn l_Lean_getPPPiBinderTypes___boxed(mut v_o_2928_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2929_: u8 = 0;
    let mut v_r_2930_: *mut LeanObject = core::ptr::null_mut();
    v_res_2929_ = l_Lean_getPPPiBinderTypes(v_o_2928_);
    lean_dec_ref(v_o_2928_);
    v_r_2930_ = lean_box((v_res_2929_) as usize);
    return v_r_2930_;
}
pub unsafe fn l_Lean_getPPPiBinderNames(mut v_o_2931_: *mut LeanObject) -> u8 {
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    v___x_2932_ = l_Lean_pp_piBinderNames;
    v_name_2933_ = lean_ctor_get(v___x_2932_, 0);
    v_map_2934_ = lean_ctor_get(v_o_2931_, 0);
    v___x_2935_ = l_Lean_getPPAll(v_o_2931_);
    v___x_2936_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2934_,
            v_name_2933_,
        );
    if lean_obj_tag(v___x_2936_) == 0 {
        return v___x_2935_;
    } else {
        let mut v_val_2937_: *mut LeanObject = core::ptr::null_mut();
        v_val_2937_ = lean_ctor_get(v___x_2936_, 0);
        lean_inc(v_val_2937_);
        lean_dec_ref_known(v___x_2936_, 1);
        if lean_obj_tag(v_val_2937_) == 1 {
            let mut v_v_2938_: u8 = 0;
            v_v_2938_ = lean_ctor_get_uint8(v_val_2937_, 0 as u32);
            lean_dec_ref_known(v_val_2937_, 0);
            return v_v_2938_;
        } else {
            lean_dec(v_val_2937_);
            return v___x_2935_;
        }
    }
}
pub unsafe fn l_Lean_getPPPiBinderNames___boxed(mut v_o_2939_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2940_: u8 = 0;
    let mut v_r_2941_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_getPPPiBinderNames(v_o_2939_);
    lean_dec_ref(v_o_2939_);
    v_r_2941_ = lean_box((v_res_2940_) as usize);
    return v_r_2941_;
}
pub unsafe fn l_Lean_getPPPiBinderNamesHygienic(mut v_o_2942_: *mut LeanObject) -> u8 {
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    v___x_2943_ = l_Lean_pp_piBinderNames_hygienic;
    v_name_2944_ = lean_ctor_get(v___x_2943_, 0);
    v_defValue_2945_ = lean_ctor_get(v___x_2943_, 1);
    v_map_2946_ = lean_ctor_get(v_o_2942_, 0);
    v___x_2947_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2946_,
            v_name_2944_,
        );
    if lean_obj_tag(v___x_2947_) == 0 {
        let mut v___x_2948_: u8 = 0;
        v___x_2948_ = (lean_unbox(v_defValue_2945_) as u8);
        return v___x_2948_;
    } else {
        let mut v_val_2949_: *mut LeanObject = core::ptr::null_mut();
        v_val_2949_ = lean_ctor_get(v___x_2947_, 0);
        lean_inc(v_val_2949_);
        lean_dec_ref_known(v___x_2947_, 1);
        if lean_obj_tag(v_val_2949_) == 1 {
            let mut v_v_2950_: u8 = 0;
            v_v_2950_ = lean_ctor_get_uint8(v_val_2949_, 0 as u32);
            lean_dec_ref_known(v_val_2949_, 0);
            return v_v_2950_;
        } else {
            let mut v___x_2951_: u8 = 0;
            lean_dec(v_val_2949_);
            v___x_2951_ = (lean_unbox(v_defValue_2945_) as u8);
            return v___x_2951_;
        }
    }
}
pub unsafe fn l_Lean_getPPPiBinderNamesHygienic___boxed(
    mut v_o_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2953_: u8 = 0;
    let mut v_r_2954_: *mut LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Lean_getPPPiBinderNamesHygienic(v_o_2952_);
    lean_dec_ref(v_o_2952_);
    v_r_2954_ = lean_box((v_res_2953_) as usize);
    return v_r_2954_;
}
pub unsafe fn l_Lean_getPPLetVarTypes(mut v_o_2955_: *mut LeanObject) -> u8 {
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    v___x_2956_ = l_Lean_pp_letVarTypes;
    v_name_2957_ = lean_ctor_get(v___x_2956_, 0);
    v_map_2958_ = lean_ctor_get(v_o_2955_, 0);
    v___x_2959_ = l_Lean_getPPAll(v_o_2955_);
    v___x_2960_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2958_,
            v_name_2957_,
        );
    if lean_obj_tag(v___x_2960_) == 0 {
        return v___x_2959_;
    } else {
        let mut v_val_2961_: *mut LeanObject = core::ptr::null_mut();
        v_val_2961_ = lean_ctor_get(v___x_2960_, 0);
        lean_inc(v_val_2961_);
        lean_dec_ref_known(v___x_2960_, 1);
        if lean_obj_tag(v_val_2961_) == 1 {
            let mut v_v_2962_: u8 = 0;
            v_v_2962_ = lean_ctor_get_uint8(v_val_2961_, 0 as u32);
            lean_dec_ref_known(v_val_2961_, 0);
            return v_v_2962_;
        } else {
            lean_dec(v_val_2961_);
            return v___x_2959_;
        }
    }
}
pub unsafe fn l_Lean_getPPLetVarTypes___boxed(mut v_o_2963_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2964_: u8 = 0;
    let mut v_r_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2964_ = l_Lean_getPPLetVarTypes(v_o_2963_);
    lean_dec_ref(v_o_2963_);
    v_r_2965_ = lean_box((v_res_2964_) as usize);
    return v_r_2965_;
}
pub unsafe fn l_Lean_getPPNumericTypes(mut v_o_2966_: *mut LeanObject) -> u8 {
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    v___x_2967_ = l_Lean_pp_numericTypes;
    v_name_2968_ = lean_ctor_get(v___x_2967_, 0);
    v_defValue_2969_ = lean_ctor_get(v___x_2967_, 1);
    v_map_2970_ = lean_ctor_get(v_o_2966_, 0);
    v___x_2971_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2970_,
            v_name_2968_,
        );
    if lean_obj_tag(v___x_2971_) == 0 {
        let mut v___x_2972_: u8 = 0;
        v___x_2972_ = (lean_unbox(v_defValue_2969_) as u8);
        return v___x_2972_;
    } else {
        let mut v_val_2973_: *mut LeanObject = core::ptr::null_mut();
        v_val_2973_ = lean_ctor_get(v___x_2971_, 0);
        lean_inc(v_val_2973_);
        lean_dec_ref_known(v___x_2971_, 1);
        if lean_obj_tag(v_val_2973_) == 1 {
            let mut v_v_2974_: u8 = 0;
            v_v_2974_ = lean_ctor_get_uint8(v_val_2973_, 0 as u32);
            lean_dec_ref_known(v_val_2973_, 0);
            return v_v_2974_;
        } else {
            let mut v___x_2975_: u8 = 0;
            lean_dec(v_val_2973_);
            v___x_2975_ = (lean_unbox(v_defValue_2969_) as u8);
            return v___x_2975_;
        }
    }
}
pub unsafe fn l_Lean_getPPNumericTypes___boxed(mut v_o_2976_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2977_: u8 = 0;
    let mut v_r_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Lean_getPPNumericTypes(v_o_2976_);
    lean_dec_ref(v_o_2976_);
    v_r_2978_ = lean_box((v_res_2977_) as usize);
    return v_r_2978_;
}
pub unsafe fn l_Lean_getPPNatLit(mut v_o_2979_: *mut LeanObject) -> u8 {
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2983_: u8 = 0;
    let mut v_map_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2987_: u8 = 0;
    let mut v___x_2988_: u8 = 0;
    let mut v___x_2989_: u8 = 0;
    let mut v___x_2990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2980_ = l_Lean_pp_natLit;
                v_name_2981_ = lean_ctor_get(v___x_2980_, 0);
                v___x_2988_ = l_Lean_getPPNumericTypes(v_o_2979_);
                if v___x_2988_ == 0 {
                    v___y_2983_ = v___x_2988_;
                    state = 1;
                    continue;
                } else {
                    v___x_2989_ = l_Lean_getPPAll(v_o_2979_);
                    if v___x_2989_ == 0 {
                        v___y_2983_ = v___x_2988_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2990_ = 0;
                        v___y_2983_ = v___x_2990_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_map_2984_ = lean_ctor_get(v_o_2979_, 0);
                v___x_2985_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2984_, v_name_2981_);
                if lean_obj_tag(v___x_2985_) == 0 {
                    return v___y_2983_;
                } else {
                    v_val_2986_ = lean_ctor_get(v___x_2985_, 0);
                    lean_inc(v_val_2986_);
                    lean_dec_ref_known(v___x_2985_, 1);
                    if lean_obj_tag(v_val_2986_) == 1 {
                        v_v_2987_ = lean_ctor_get_uint8(v_val_2986_, 0 as u32);
                        lean_dec_ref_known(v_val_2986_, 0);
                        return v_v_2987_;
                    } else {
                        lean_dec(v_val_2986_);
                        return v___y_2983_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPNatLit___boxed(mut v_o_2991_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2992_: u8 = 0;
    let mut v_r_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_Lean_getPPNatLit(v_o_2991_);
    lean_dec_ref(v_o_2991_);
    v_r_2993_ = lean_box((v_res_2992_) as usize);
    return v_r_2993_;
}
pub unsafe fn l_Lean_getPPCoercions(mut v_o_2994_: *mut LeanObject) -> u8 {
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2998_: u8 = 0;
    let mut v_map_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3002_: u8 = 0;
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: u8 = 0;
    let mut v___x_3005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2995_ = l_Lean_pp_coercions;
                v_name_2996_ = lean_ctor_get(v___x_2995_, 0);
                v___x_3003_ = l_Lean_getPPAll(v_o_2994_);
                if v___x_3003_ == 0 {
                    v___x_3004_ = 1;
                    v___y_2998_ = v___x_3004_;
                    state = 1;
                    continue;
                } else {
                    v___x_3005_ = 0;
                    v___y_2998_ = v___x_3005_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_2999_ = lean_ctor_get(v_o_2994_, 0);
                v___x_3000_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2999_, v_name_2996_);
                if lean_obj_tag(v___x_3000_) == 0 {
                    return v___y_2998_;
                } else {
                    v_val_3001_ = lean_ctor_get(v___x_3000_, 0);
                    lean_inc(v_val_3001_);
                    lean_dec_ref_known(v___x_3000_, 1);
                    if lean_obj_tag(v_val_3001_) == 1 {
                        v_v_3002_ = lean_ctor_get_uint8(v_val_3001_, 0 as u32);
                        lean_dec_ref_known(v_val_3001_, 0);
                        return v_v_3002_;
                    } else {
                        lean_dec(v_val_3001_);
                        return v___y_2998_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPCoercions___boxed(mut v_o_3006_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3007_: u8 = 0;
    let mut v_r_3008_: *mut LeanObject = core::ptr::null_mut();
    v_res_3007_ = l_Lean_getPPCoercions(v_o_3006_);
    lean_dec_ref(v_o_3006_);
    v_r_3008_ = lean_box((v_res_3007_) as usize);
    return v_r_3008_;
}
pub unsafe fn l_Lean_getPPCoercionsTypes(mut v_o_3009_: *mut LeanObject) -> u8 {
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    v___x_3010_ = l_Lean_pp_coercions_types;
    v_name_3011_ = lean_ctor_get(v___x_3010_, 0);
    v_defValue_3012_ = lean_ctor_get(v___x_3010_, 1);
    v_map_3013_ = lean_ctor_get(v_o_3009_, 0);
    v___x_3014_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3013_,
            v_name_3011_,
        );
    if lean_obj_tag(v___x_3014_) == 0 {
        let mut v___x_3015_: u8 = 0;
        v___x_3015_ = (lean_unbox(v_defValue_3012_) as u8);
        return v___x_3015_;
    } else {
        let mut v_val_3016_: *mut LeanObject = core::ptr::null_mut();
        v_val_3016_ = lean_ctor_get(v___x_3014_, 0);
        lean_inc(v_val_3016_);
        lean_dec_ref_known(v___x_3014_, 1);
        if lean_obj_tag(v_val_3016_) == 1 {
            let mut v_v_3017_: u8 = 0;
            v_v_3017_ = lean_ctor_get_uint8(v_val_3016_, 0 as u32);
            lean_dec_ref_known(v_val_3016_, 0);
            return v_v_3017_;
        } else {
            let mut v___x_3018_: u8 = 0;
            lean_dec(v_val_3016_);
            v___x_3018_ = (lean_unbox(v_defValue_3012_) as u8);
            return v___x_3018_;
        }
    }
}
pub unsafe fn l_Lean_getPPCoercionsTypes___boxed(
    mut v_o_3019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3020_: u8 = 0;
    let mut v_r_3021_: *mut LeanObject = core::ptr::null_mut();
    v_res_3020_ = l_Lean_getPPCoercionsTypes(v_o_3019_);
    lean_dec_ref(v_o_3019_);
    v_r_3021_ = lean_box((v_res_3020_) as usize);
    return v_r_3021_;
}
pub unsafe fn l_Lean_getPPExplicit(mut v_o_3022_: *mut LeanObject) -> u8 {
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    v___x_3023_ = l_Lean_pp_explicit;
    v_name_3024_ = lean_ctor_get(v___x_3023_, 0);
    v_map_3025_ = lean_ctor_get(v_o_3022_, 0);
    v___x_3026_ = l_Lean_getPPAll(v_o_3022_);
    v___x_3027_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3025_,
            v_name_3024_,
        );
    if lean_obj_tag(v___x_3027_) == 0 {
        return v___x_3026_;
    } else {
        let mut v_val_3028_: *mut LeanObject = core::ptr::null_mut();
        v_val_3028_ = lean_ctor_get(v___x_3027_, 0);
        lean_inc(v_val_3028_);
        lean_dec_ref_known(v___x_3027_, 1);
        if lean_obj_tag(v_val_3028_) == 1 {
            let mut v_v_3029_: u8 = 0;
            v_v_3029_ = lean_ctor_get_uint8(v_val_3028_, 0 as u32);
            lean_dec_ref_known(v_val_3028_, 0);
            return v_v_3029_;
        } else {
            lean_dec(v_val_3028_);
            return v___x_3026_;
        }
    }
}
pub unsafe fn l_Lean_getPPExplicit___boxed(mut v_o_3030_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3031_: u8 = 0;
    let mut v_r_3032_: *mut LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_getPPExplicit(v_o_3030_);
    lean_dec_ref(v_o_3030_);
    v_r_3032_ = lean_box((v_res_3031_) as usize);
    return v_r_3032_;
}
pub unsafe fn l_Lean_getPPForalls(mut v_o_3033_: *mut LeanObject) -> u8 {
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    v___x_3034_ = l_Lean_pp_foralls;
    v_name_3035_ = lean_ctor_get(v___x_3034_, 0);
    v_defValue_3036_ = lean_ctor_get(v___x_3034_, 1);
    v_map_3037_ = lean_ctor_get(v_o_3033_, 0);
    v___x_3038_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3037_,
            v_name_3035_,
        );
    if lean_obj_tag(v___x_3038_) == 0 {
        let mut v___x_3039_: u8 = 0;
        v___x_3039_ = (lean_unbox(v_defValue_3036_) as u8);
        return v___x_3039_;
    } else {
        let mut v_val_3040_: *mut LeanObject = core::ptr::null_mut();
        v_val_3040_ = lean_ctor_get(v___x_3038_, 0);
        lean_inc(v_val_3040_);
        lean_dec_ref_known(v___x_3038_, 1);
        if lean_obj_tag(v_val_3040_) == 1 {
            let mut v_v_3041_: u8 = 0;
            v_v_3041_ = lean_ctor_get_uint8(v_val_3040_, 0 as u32);
            lean_dec_ref_known(v_val_3040_, 0);
            return v_v_3041_;
        } else {
            let mut v___x_3042_: u8 = 0;
            lean_dec(v_val_3040_);
            v___x_3042_ = (lean_unbox(v_defValue_3036_) as u8);
            return v___x_3042_;
        }
    }
}
pub unsafe fn l_Lean_getPPForalls___boxed(mut v_o_3043_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3044_: u8 = 0;
    let mut v_r_3045_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Lean_getPPForalls(v_o_3043_);
    lean_dec_ref(v_o_3043_);
    v_r_3045_ = lean_box((v_res_3044_) as usize);
    return v_r_3045_;
}
pub unsafe fn l_Lean_getPPNotation(mut v_o_3046_: *mut LeanObject) -> u8 {
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: u8 = 0;
    let mut v_map_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3054_: u8 = 0;
    let mut v___x_3055_: u8 = 0;
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3047_ = l_Lean_pp_notation;
                v_name_3048_ = lean_ctor_get(v___x_3047_, 0);
                v___x_3055_ = l_Lean_getPPAll(v_o_3046_);
                if v___x_3055_ == 0 {
                    v___x_3056_ = 1;
                    v___y_3050_ = v___x_3056_;
                    state = 1;
                    continue;
                } else {
                    v___x_3057_ = 0;
                    v___y_3050_ = v___x_3057_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3051_ = lean_ctor_get(v_o_3046_, 0);
                v___x_3052_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3051_, v_name_3048_);
                if lean_obj_tag(v___x_3052_) == 0 {
                    return v___y_3050_;
                } else {
                    v_val_3053_ = lean_ctor_get(v___x_3052_, 0);
                    lean_inc(v_val_3053_);
                    lean_dec_ref_known(v___x_3052_, 1);
                    if lean_obj_tag(v_val_3053_) == 1 {
                        v_v_3054_ = lean_ctor_get_uint8(v_val_3053_, 0 as u32);
                        lean_dec_ref_known(v_val_3053_, 0);
                        return v_v_3054_;
                    } else {
                        lean_dec(v_val_3053_);
                        return v___y_3050_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPNotation___boxed(mut v_o_3058_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3059_: u8 = 0;
    let mut v_r_3060_: *mut LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Lean_getPPNotation(v_o_3058_);
    lean_dec_ref(v_o_3058_);
    v_r_3060_ = lean_box((v_res_3059_) as usize);
    return v_r_3060_;
}
pub unsafe fn l_Lean_getPPParens(mut v_o_3061_: *mut LeanObject) -> u8 {
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    v___x_3062_ = l_Lean_pp_parens;
    v_name_3063_ = lean_ctor_get(v___x_3062_, 0);
    v_defValue_3064_ = lean_ctor_get(v___x_3062_, 1);
    v_map_3065_ = lean_ctor_get(v_o_3061_, 0);
    v___x_3066_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3065_,
            v_name_3063_,
        );
    if lean_obj_tag(v___x_3066_) == 0 {
        let mut v___x_3067_: u8 = 0;
        v___x_3067_ = (lean_unbox(v_defValue_3064_) as u8);
        return v___x_3067_;
    } else {
        let mut v_val_3068_: *mut LeanObject = core::ptr::null_mut();
        v_val_3068_ = lean_ctor_get(v___x_3066_, 0);
        lean_inc(v_val_3068_);
        lean_dec_ref_known(v___x_3066_, 1);
        if lean_obj_tag(v_val_3068_) == 1 {
            let mut v_v_3069_: u8 = 0;
            v_v_3069_ = lean_ctor_get_uint8(v_val_3068_, 0 as u32);
            lean_dec_ref_known(v_val_3068_, 0);
            return v_v_3069_;
        } else {
            let mut v___x_3070_: u8 = 0;
            lean_dec(v_val_3068_);
            v___x_3070_ = (lean_unbox(v_defValue_3064_) as u8);
            return v___x_3070_;
        }
    }
}
pub unsafe fn l_Lean_getPPParens___boxed(mut v_o_3071_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3072_: u8 = 0;
    let mut v_r_3073_: *mut LeanObject = core::ptr::null_mut();
    v_res_3072_ = l_Lean_getPPParens(v_o_3071_);
    lean_dec_ref(v_o_3071_);
    v_r_3073_ = lean_box((v_res_3072_) as usize);
    return v_r_3073_;
}
pub unsafe fn l_Lean_getPPUnicode(mut v_o_3074_: *mut LeanObject) -> u8 {
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    v___x_3075_ = l_Lean_pp_unicode;
    v_name_3076_ = lean_ctor_get(v___x_3075_, 0);
    v_defValue_3077_ = lean_ctor_get(v___x_3075_, 1);
    v_map_3078_ = lean_ctor_get(v_o_3074_, 0);
    v___x_3079_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3078_,
            v_name_3076_,
        );
    if lean_obj_tag(v___x_3079_) == 0 {
        let mut v___x_3080_: u8 = 0;
        v___x_3080_ = (lean_unbox(v_defValue_3077_) as u8);
        return v___x_3080_;
    } else {
        let mut v_val_3081_: *mut LeanObject = core::ptr::null_mut();
        v_val_3081_ = lean_ctor_get(v___x_3079_, 0);
        lean_inc(v_val_3081_);
        lean_dec_ref_known(v___x_3079_, 1);
        if lean_obj_tag(v_val_3081_) == 1 {
            let mut v_v_3082_: u8 = 0;
            v_v_3082_ = lean_ctor_get_uint8(v_val_3081_, 0 as u32);
            lean_dec_ref_known(v_val_3081_, 0);
            return v_v_3082_;
        } else {
            let mut v___x_3083_: u8 = 0;
            lean_dec(v_val_3081_);
            v___x_3083_ = (lean_unbox(v_defValue_3077_) as u8);
            return v___x_3083_;
        }
    }
}
pub unsafe fn l_Lean_getPPUnicode___boxed(mut v_o_3084_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3085_: u8 = 0;
    let mut v_r_3086_: *mut LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lean_getPPUnicode(v_o_3084_);
    lean_dec_ref(v_o_3084_);
    v_r_3086_ = lean_box((v_res_3085_) as usize);
    return v_r_3086_;
}
pub unsafe fn l_Lean_getPPUnicodeFun(mut v_o_3087_: *mut LeanObject) -> u8 {
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    v___x_3088_ = l_Lean_pp_unicode_fun;
    v_name_3089_ = lean_ctor_get(v___x_3088_, 0);
    v_defValue_3090_ = lean_ctor_get(v___x_3088_, 1);
    v_map_3091_ = lean_ctor_get(v_o_3087_, 0);
    v___x_3092_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3091_,
            v_name_3089_,
        );
    if lean_obj_tag(v___x_3092_) == 0 {
        let mut v___x_3093_: u8 = 0;
        v___x_3093_ = (lean_unbox(v_defValue_3090_) as u8);
        return v___x_3093_;
    } else {
        let mut v_val_3094_: *mut LeanObject = core::ptr::null_mut();
        v_val_3094_ = lean_ctor_get(v___x_3092_, 0);
        lean_inc(v_val_3094_);
        lean_dec_ref_known(v___x_3092_, 1);
        if lean_obj_tag(v_val_3094_) == 1 {
            let mut v_v_3095_: u8 = 0;
            v_v_3095_ = lean_ctor_get_uint8(v_val_3094_, 0 as u32);
            lean_dec_ref_known(v_val_3094_, 0);
            return v_v_3095_;
        } else {
            let mut v___x_3096_: u8 = 0;
            lean_dec(v_val_3094_);
            v___x_3096_ = (lean_unbox(v_defValue_3090_) as u8);
            return v___x_3096_;
        }
    }
}
pub unsafe fn l_Lean_getPPUnicodeFun___boxed(mut v_o_3097_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3098_: u8 = 0;
    let mut v_r_3099_: *mut LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Lean_getPPUnicodeFun(v_o_3097_);
    lean_dec_ref(v_o_3097_);
    v_r_3099_ = lean_box((v_res_3098_) as usize);
    return v_r_3099_;
}
pub unsafe fn l_Lean_getPPMatch(mut v_o_3100_: *mut LeanObject) -> u8 {
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3104_: u8 = 0;
    let mut v_map_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3108_: u8 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3101_ = l_Lean_pp_match;
                v_name_3102_ = lean_ctor_get(v___x_3101_, 0);
                v___x_3109_ = l_Lean_getPPAll(v_o_3100_);
                if v___x_3109_ == 0 {
                    v___x_3110_ = 1;
                    v___y_3104_ = v___x_3110_;
                    state = 1;
                    continue;
                } else {
                    v___x_3111_ = 0;
                    v___y_3104_ = v___x_3111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3105_ = lean_ctor_get(v_o_3100_, 0);
                v___x_3106_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3105_, v_name_3102_);
                if lean_obj_tag(v___x_3106_) == 0 {
                    return v___y_3104_;
                } else {
                    v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
                    lean_inc(v_val_3107_);
                    lean_dec_ref_known(v___x_3106_, 1);
                    if lean_obj_tag(v_val_3107_) == 1 {
                        v_v_3108_ = lean_ctor_get_uint8(v_val_3107_, 0 as u32);
                        lean_dec_ref_known(v_val_3107_, 0);
                        return v_v_3108_;
                    } else {
                        lean_dec(v_val_3107_);
                        return v___y_3104_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPMatch___boxed(mut v_o_3112_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3113_: u8 = 0;
    let mut v_r_3114_: *mut LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_getPPMatch(v_o_3112_);
    lean_dec_ref(v_o_3112_);
    v_r_3114_ = lean_box((v_res_3113_) as usize);
    return v_r_3114_;
}
pub unsafe fn l_Lean_getPPSorrySource(mut v_o_3115_: *mut LeanObject) -> u8 {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    v___x_3116_ = l_Lean_pp_sorrySource;
    v_name_3117_ = lean_ctor_get(v___x_3116_, 0);
    v_defValue_3118_ = lean_ctor_get(v___x_3116_, 1);
    v_map_3119_ = lean_ctor_get(v_o_3115_, 0);
    v___x_3120_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3119_,
            v_name_3117_,
        );
    if lean_obj_tag(v___x_3120_) == 0 {
        let mut v___x_3121_: u8 = 0;
        v___x_3121_ = (lean_unbox(v_defValue_3118_) as u8);
        return v___x_3121_;
    } else {
        let mut v_val_3122_: *mut LeanObject = core::ptr::null_mut();
        v_val_3122_ = lean_ctor_get(v___x_3120_, 0);
        lean_inc(v_val_3122_);
        lean_dec_ref_known(v___x_3120_, 1);
        if lean_obj_tag(v_val_3122_) == 1 {
            let mut v_v_3123_: u8 = 0;
            v_v_3123_ = lean_ctor_get_uint8(v_val_3122_, 0 as u32);
            lean_dec_ref_known(v_val_3122_, 0);
            return v_v_3123_;
        } else {
            let mut v___x_3124_: u8 = 0;
            lean_dec(v_val_3122_);
            v___x_3124_ = (lean_unbox(v_defValue_3118_) as u8);
            return v___x_3124_;
        }
    }
}
pub unsafe fn l_Lean_getPPSorrySource___boxed(mut v_o_3125_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3126_: u8 = 0;
    let mut v_r_3127_: *mut LeanObject = core::ptr::null_mut();
    v_res_3126_ = l_Lean_getPPSorrySource(v_o_3125_);
    lean_dec_ref(v_o_3125_);
    v_r_3127_ = lean_box((v_res_3126_) as usize);
    return v_r_3127_;
}
pub unsafe fn l_Lean_getPPFieldNotation(mut v_o_3128_: *mut LeanObject) -> u8 {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3132_: u8 = 0;
    let mut v_map_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3136_: u8 = 0;
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: u8 = 0;
    let mut v___x_3139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3129_ = l_Lean_pp_fieldNotation;
                v_name_3130_ = lean_ctor_get(v___x_3129_, 0);
                v___x_3137_ = l_Lean_getPPAll(v_o_3128_);
                if v___x_3137_ == 0 {
                    v___x_3138_ = 1;
                    v___y_3132_ = v___x_3138_;
                    state = 1;
                    continue;
                } else {
                    v___x_3139_ = 0;
                    v___y_3132_ = v___x_3139_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3133_ = lean_ctor_get(v_o_3128_, 0);
                v___x_3134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3133_, v_name_3130_);
                if lean_obj_tag(v___x_3134_) == 0 {
                    return v___y_3132_;
                } else {
                    v_val_3135_ = lean_ctor_get(v___x_3134_, 0);
                    lean_inc(v_val_3135_);
                    lean_dec_ref_known(v___x_3134_, 1);
                    if lean_obj_tag(v_val_3135_) == 1 {
                        v_v_3136_ = lean_ctor_get_uint8(v_val_3135_, 0 as u32);
                        lean_dec_ref_known(v_val_3135_, 0);
                        return v_v_3136_;
                    } else {
                        lean_dec(v_val_3135_);
                        return v___y_3132_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPFieldNotation___boxed(mut v_o_3140_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3141_: u8 = 0;
    let mut v_r_3142_: *mut LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Lean_getPPFieldNotation(v_o_3140_);
    lean_dec_ref(v_o_3140_);
    v_r_3142_ = lean_box((v_res_3141_) as usize);
    return v_r_3142_;
}
pub unsafe fn l_Lean_getPPFieldNotationGeneralized(mut v_o_3143_: *mut LeanObject) -> u8 {
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    v___x_3144_ = l_Lean_pp_fieldNotation_generalized;
    v_name_3145_ = lean_ctor_get(v___x_3144_, 0);
    v_defValue_3146_ = lean_ctor_get(v___x_3144_, 1);
    v_map_3147_ = lean_ctor_get(v_o_3143_, 0);
    v___x_3148_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3147_,
            v_name_3145_,
        );
    if lean_obj_tag(v___x_3148_) == 0 {
        let mut v___x_3149_: u8 = 0;
        v___x_3149_ = (lean_unbox(v_defValue_3146_) as u8);
        return v___x_3149_;
    } else {
        let mut v_val_3150_: *mut LeanObject = core::ptr::null_mut();
        v_val_3150_ = lean_ctor_get(v___x_3148_, 0);
        lean_inc(v_val_3150_);
        lean_dec_ref_known(v___x_3148_, 1);
        if lean_obj_tag(v_val_3150_) == 1 {
            let mut v_v_3151_: u8 = 0;
            v_v_3151_ = lean_ctor_get_uint8(v_val_3150_, 0 as u32);
            lean_dec_ref_known(v_val_3150_, 0);
            return v_v_3151_;
        } else {
            let mut v___x_3152_: u8 = 0;
            lean_dec(v_val_3150_);
            v___x_3152_ = (lean_unbox(v_defValue_3146_) as u8);
            return v___x_3152_;
        }
    }
}
pub unsafe fn l_Lean_getPPFieldNotationGeneralized___boxed(
    mut v_o_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3154_: u8 = 0;
    let mut v_r_3155_: *mut LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_getPPFieldNotationGeneralized(v_o_3153_);
    lean_dec_ref(v_o_3153_);
    v_r_3155_ = lean_box((v_res_3154_) as usize);
    return v_r_3155_;
}
pub unsafe fn l_Lean_getPPStructureInstances(mut v_o_3156_: *mut LeanObject) -> u8 {
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: u8 = 0;
    let mut v_map_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3164_: u8 = 0;
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: u8 = 0;
    let mut v___x_3167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3157_ = l_Lean_pp_structureInstances;
                v_name_3158_ = lean_ctor_get(v___x_3157_, 0);
                v___x_3165_ = l_Lean_getPPAll(v_o_3156_);
                if v___x_3165_ == 0 {
                    v___x_3166_ = 1;
                    v___y_3160_ = v___x_3166_;
                    state = 1;
                    continue;
                } else {
                    v___x_3167_ = 0;
                    v___y_3160_ = v___x_3167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3161_ = lean_ctor_get(v_o_3156_, 0);
                v___x_3162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3161_, v_name_3158_);
                if lean_obj_tag(v___x_3162_) == 0 {
                    return v___y_3160_;
                } else {
                    v_val_3163_ = lean_ctor_get(v___x_3162_, 0);
                    lean_inc(v_val_3163_);
                    lean_dec_ref_known(v___x_3162_, 1);
                    if lean_obj_tag(v_val_3163_) == 1 {
                        v_v_3164_ = lean_ctor_get_uint8(v_val_3163_, 0 as u32);
                        lean_dec_ref_known(v_val_3163_, 0);
                        return v_v_3164_;
                    } else {
                        lean_dec(v_val_3163_);
                        return v___y_3160_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPStructureInstances___boxed(
    mut v_o_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3169_: u8 = 0;
    let mut v_r_3170_: *mut LeanObject = core::ptr::null_mut();
    v_res_3169_ = l_Lean_getPPStructureInstances(v_o_3168_);
    lean_dec_ref(v_o_3168_);
    v_r_3170_ = lean_box((v_res_3169_) as usize);
    return v_r_3170_;
}
pub unsafe fn l_Lean_getPPStructureInstancesFlatten(mut v_o_3171_: *mut LeanObject) -> u8 {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    v___x_3172_ = l_Lean_pp_structureInstances_flatten;
    v_name_3173_ = lean_ctor_get(v___x_3172_, 0);
    v_defValue_3174_ = lean_ctor_get(v___x_3172_, 1);
    v_map_3175_ = lean_ctor_get(v_o_3171_, 0);
    v___x_3176_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3175_,
            v_name_3173_,
        );
    if lean_obj_tag(v___x_3176_) == 0 {
        let mut v___x_3177_: u8 = 0;
        v___x_3177_ = (lean_unbox(v_defValue_3174_) as u8);
        return v___x_3177_;
    } else {
        let mut v_val_3178_: *mut LeanObject = core::ptr::null_mut();
        v_val_3178_ = lean_ctor_get(v___x_3176_, 0);
        lean_inc(v_val_3178_);
        lean_dec_ref_known(v___x_3176_, 1);
        if lean_obj_tag(v_val_3178_) == 1 {
            let mut v_v_3179_: u8 = 0;
            v_v_3179_ = lean_ctor_get_uint8(v_val_3178_, 0 as u32);
            lean_dec_ref_known(v_val_3178_, 0);
            return v_v_3179_;
        } else {
            let mut v___x_3180_: u8 = 0;
            lean_dec(v_val_3178_);
            v___x_3180_ = (lean_unbox(v_defValue_3174_) as u8);
            return v___x_3180_;
        }
    }
}
pub unsafe fn l_Lean_getPPStructureInstancesFlatten___boxed(
    mut v_o_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3182_: u8 = 0;
    let mut v_r_3183_: *mut LeanObject = core::ptr::null_mut();
    v_res_3182_ = l_Lean_getPPStructureInstancesFlatten(v_o_3181_);
    lean_dec_ref(v_o_3181_);
    v_r_3183_ = lean_box((v_res_3182_) as usize);
    return v_r_3183_;
}
pub unsafe fn l_Lean_getPPStructureInstancesDefaults(mut v_o_3184_: *mut LeanObject) -> u8 {
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    v___x_3185_ = l_Lean_pp_structureInstances_defaults;
    v_name_3186_ = lean_ctor_get(v___x_3185_, 0);
    v_defValue_3187_ = lean_ctor_get(v___x_3185_, 1);
    v_map_3188_ = lean_ctor_get(v_o_3184_, 0);
    v___x_3189_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3188_,
            v_name_3186_,
        );
    if lean_obj_tag(v___x_3189_) == 0 {
        let mut v___x_3190_: u8 = 0;
        v___x_3190_ = (lean_unbox(v_defValue_3187_) as u8);
        return v___x_3190_;
    } else {
        let mut v_val_3191_: *mut LeanObject = core::ptr::null_mut();
        v_val_3191_ = lean_ctor_get(v___x_3189_, 0);
        lean_inc(v_val_3191_);
        lean_dec_ref_known(v___x_3189_, 1);
        if lean_obj_tag(v_val_3191_) == 1 {
            let mut v_v_3192_: u8 = 0;
            v_v_3192_ = lean_ctor_get_uint8(v_val_3191_, 0 as u32);
            lean_dec_ref_known(v_val_3191_, 0);
            return v_v_3192_;
        } else {
            let mut v___x_3193_: u8 = 0;
            lean_dec(v_val_3191_);
            v___x_3193_ = (lean_unbox(v_defValue_3187_) as u8);
            return v___x_3193_;
        }
    }
}
pub unsafe fn l_Lean_getPPStructureInstancesDefaults___boxed(
    mut v_o_3194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3195_: u8 = 0;
    let mut v_r_3196_: *mut LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_Lean_getPPStructureInstancesDefaults(v_o_3194_);
    lean_dec_ref(v_o_3194_);
    v_r_3196_ = lean_box((v_res_3195_) as usize);
    return v_r_3196_;
}
pub unsafe fn l_Lean_getPPStructureInstanceType(mut v_o_3197_: *mut LeanObject) -> u8 {
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    v___x_3198_ = l_Lean_pp_structureInstanceTypes;
    v_name_3199_ = lean_ctor_get(v___x_3198_, 0);
    v_map_3200_ = lean_ctor_get(v_o_3197_, 0);
    v___x_3201_ = l_Lean_getPPAll(v_o_3197_);
    v___x_3202_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3200_,
            v_name_3199_,
        );
    if lean_obj_tag(v___x_3202_) == 0 {
        return v___x_3201_;
    } else {
        let mut v_val_3203_: *mut LeanObject = core::ptr::null_mut();
        v_val_3203_ = lean_ctor_get(v___x_3202_, 0);
        lean_inc(v_val_3203_);
        lean_dec_ref_known(v___x_3202_, 1);
        if lean_obj_tag(v_val_3203_) == 1 {
            let mut v_v_3204_: u8 = 0;
            v_v_3204_ = lean_ctor_get_uint8(v_val_3203_, 0 as u32);
            lean_dec_ref_known(v_val_3203_, 0);
            return v_v_3204_;
        } else {
            lean_dec(v_val_3203_);
            return v___x_3201_;
        }
    }
}
pub unsafe fn l_Lean_getPPStructureInstanceType___boxed(
    mut v_o_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3206_: u8 = 0;
    let mut v_r_3207_: *mut LeanObject = core::ptr::null_mut();
    v_res_3206_ = l_Lean_getPPStructureInstanceType(v_o_3205_);
    lean_dec_ref(v_o_3205_);
    v_r_3207_ = lean_box((v_res_3206_) as usize);
    return v_r_3207_;
}
pub unsafe fn l_Lean_getPPTagAppFns(mut v_o_3208_: *mut LeanObject) -> u8 {
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    v___x_3209_ = l_Lean_pp_tagAppFns;
    v_name_3210_ = lean_ctor_get(v___x_3209_, 0);
    v_map_3211_ = lean_ctor_get(v_o_3208_, 0);
    v___x_3212_ = l_Lean_getPPAll(v_o_3208_);
    v___x_3213_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3211_,
            v_name_3210_,
        );
    if lean_obj_tag(v___x_3213_) == 0 {
        return v___x_3212_;
    } else {
        let mut v_val_3214_: *mut LeanObject = core::ptr::null_mut();
        v_val_3214_ = lean_ctor_get(v___x_3213_, 0);
        lean_inc(v_val_3214_);
        lean_dec_ref_known(v___x_3213_, 1);
        if lean_obj_tag(v_val_3214_) == 1 {
            let mut v_v_3215_: u8 = 0;
            v_v_3215_ = lean_ctor_get_uint8(v_val_3214_, 0 as u32);
            lean_dec_ref_known(v_val_3214_, 0);
            return v_v_3215_;
        } else {
            lean_dec(v_val_3214_);
            return v___x_3212_;
        }
    }
}
pub unsafe fn l_Lean_getPPTagAppFns___boxed(mut v_o_3216_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3217_: u8 = 0;
    let mut v_r_3218_: *mut LeanObject = core::ptr::null_mut();
    v_res_3217_ = l_Lean_getPPTagAppFns(v_o_3216_);
    lean_dec_ref(v_o_3216_);
    v_r_3218_ = lean_box((v_res_3217_) as usize);
    return v_r_3218_;
}
pub unsafe fn l_Lean_getPPUniverses(mut v_o_3219_: *mut LeanObject) -> u8 {
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Lean_pp_universes;
    v_name_3221_ = lean_ctor_get(v___x_3220_, 0);
    v_map_3222_ = lean_ctor_get(v_o_3219_, 0);
    v___x_3223_ = l_Lean_getPPAll(v_o_3219_);
    v___x_3224_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3222_,
            v_name_3221_,
        );
    if lean_obj_tag(v___x_3224_) == 0 {
        return v___x_3223_;
    } else {
        let mut v_val_3225_: *mut LeanObject = core::ptr::null_mut();
        v_val_3225_ = lean_ctor_get(v___x_3224_, 0);
        lean_inc(v_val_3225_);
        lean_dec_ref_known(v___x_3224_, 1);
        if lean_obj_tag(v_val_3225_) == 1 {
            let mut v_v_3226_: u8 = 0;
            v_v_3226_ = lean_ctor_get_uint8(v_val_3225_, 0 as u32);
            lean_dec_ref_known(v_val_3225_, 0);
            return v_v_3226_;
        } else {
            lean_dec(v_val_3225_);
            return v___x_3223_;
        }
    }
}
pub unsafe fn l_Lean_getPPUniverses___boxed(mut v_o_3227_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3228_: u8 = 0;
    let mut v_r_3229_: *mut LeanObject = core::ptr::null_mut();
    v_res_3228_ = l_Lean_getPPUniverses(v_o_3227_);
    lean_dec_ref(v_o_3227_);
    v_r_3229_ = lean_box((v_res_3228_) as usize);
    return v_r_3229_;
}
pub unsafe fn l_Lean_getPPFullNames(mut v_o_3230_: *mut LeanObject) -> u8 {
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    v___x_3231_ = l_Lean_pp_fullNames;
    v_name_3232_ = lean_ctor_get(v___x_3231_, 0);
    v_map_3233_ = lean_ctor_get(v_o_3230_, 0);
    v___x_3234_ = l_Lean_getPPAll(v_o_3230_);
    v___x_3235_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3233_,
            v_name_3232_,
        );
    if lean_obj_tag(v___x_3235_) == 0 {
        return v___x_3234_;
    } else {
        let mut v_val_3236_: *mut LeanObject = core::ptr::null_mut();
        v_val_3236_ = lean_ctor_get(v___x_3235_, 0);
        lean_inc(v_val_3236_);
        lean_dec_ref_known(v___x_3235_, 1);
        if lean_obj_tag(v_val_3236_) == 1 {
            let mut v_v_3237_: u8 = 0;
            v_v_3237_ = lean_ctor_get_uint8(v_val_3236_, 0 as u32);
            lean_dec_ref_known(v_val_3236_, 0);
            return v_v_3237_;
        } else {
            lean_dec(v_val_3236_);
            return v___x_3234_;
        }
    }
}
pub unsafe fn l_Lean_getPPFullNames___boxed(mut v_o_3238_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3239_: u8 = 0;
    let mut v_r_3240_: *mut LeanObject = core::ptr::null_mut();
    v_res_3239_ = l_Lean_getPPFullNames(v_o_3238_);
    lean_dec_ref(v_o_3238_);
    v_r_3240_ = lean_box((v_res_3239_) as usize);
    return v_r_3240_;
}
pub unsafe fn l_Lean_getPPPrivateNames(mut v_o_3241_: *mut LeanObject) -> u8 {
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Lean_pp_privateNames;
    v_name_3243_ = lean_ctor_get(v___x_3242_, 0);
    v_map_3244_ = lean_ctor_get(v_o_3241_, 0);
    v___x_3245_ = l_Lean_getPPAll(v_o_3241_);
    v___x_3246_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3244_,
            v_name_3243_,
        );
    if lean_obj_tag(v___x_3246_) == 0 {
        return v___x_3245_;
    } else {
        let mut v_val_3247_: *mut LeanObject = core::ptr::null_mut();
        v_val_3247_ = lean_ctor_get(v___x_3246_, 0);
        lean_inc(v_val_3247_);
        lean_dec_ref_known(v___x_3246_, 1);
        if lean_obj_tag(v_val_3247_) == 1 {
            let mut v_v_3248_: u8 = 0;
            v_v_3248_ = lean_ctor_get_uint8(v_val_3247_, 0 as u32);
            lean_dec_ref_known(v_val_3247_, 0);
            return v_v_3248_;
        } else {
            lean_dec(v_val_3247_);
            return v___x_3245_;
        }
    }
}
pub unsafe fn l_Lean_getPPPrivateNames___boxed(mut v_o_3249_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3250_: u8 = 0;
    let mut v_r_3251_: *mut LeanObject = core::ptr::null_mut();
    v_res_3250_ = l_Lean_getPPPrivateNames(v_o_3249_);
    lean_dec_ref(v_o_3249_);
    v_r_3251_ = lean_box((v_res_3250_) as usize);
    return v_r_3251_;
}
pub unsafe fn l_Lean_getPPMData(mut v_o_3252_: *mut LeanObject) -> u8 {
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Lean_pp_mdata;
    v_name_3254_ = lean_ctor_get(v___x_3253_, 0);
    v_defValue_3255_ = lean_ctor_get(v___x_3253_, 1);
    v_map_3256_ = lean_ctor_get(v_o_3252_, 0);
    v___x_3257_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3256_,
            v_name_3254_,
        );
    if lean_obj_tag(v___x_3257_) == 0 {
        let mut v___x_3258_: u8 = 0;
        v___x_3258_ = (lean_unbox(v_defValue_3255_) as u8);
        return v___x_3258_;
    } else {
        let mut v_val_3259_: *mut LeanObject = core::ptr::null_mut();
        v_val_3259_ = lean_ctor_get(v___x_3257_, 0);
        lean_inc(v_val_3259_);
        lean_dec_ref_known(v___x_3257_, 1);
        if lean_obj_tag(v_val_3259_) == 1 {
            let mut v_v_3260_: u8 = 0;
            v_v_3260_ = lean_ctor_get_uint8(v_val_3259_, 0 as u32);
            lean_dec_ref_known(v_val_3259_, 0);
            return v_v_3260_;
        } else {
            let mut v___x_3261_: u8 = 0;
            lean_dec(v_val_3259_);
            v___x_3261_ = (lean_unbox(v_defValue_3255_) as u8);
            return v___x_3261_;
        }
    }
}
pub unsafe fn l_Lean_getPPMData___boxed(mut v_o_3262_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3263_: u8 = 0;
    let mut v_r_3264_: *mut LeanObject = core::ptr::null_mut();
    v_res_3263_ = l_Lean_getPPMData(v_o_3262_);
    lean_dec_ref(v_o_3262_);
    v_r_3264_ = lean_box((v_res_3263_) as usize);
    return v_r_3264_;
}
pub unsafe fn l_Lean_getPPInstantiateMVars(mut v_o_3265_: *mut LeanObject) -> u8 {
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    v___x_3266_ = l_Lean_pp_instantiateMVars;
    v_name_3267_ = lean_ctor_get(v___x_3266_, 0);
    v_defValue_3268_ = lean_ctor_get(v___x_3266_, 1);
    v_map_3269_ = lean_ctor_get(v_o_3265_, 0);
    v___x_3270_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3269_,
            v_name_3267_,
        );
    if lean_obj_tag(v___x_3270_) == 0 {
        let mut v___x_3271_: u8 = 0;
        v___x_3271_ = (lean_unbox(v_defValue_3268_) as u8);
        return v___x_3271_;
    } else {
        let mut v_val_3272_: *mut LeanObject = core::ptr::null_mut();
        v_val_3272_ = lean_ctor_get(v___x_3270_, 0);
        lean_inc(v_val_3272_);
        lean_dec_ref_known(v___x_3270_, 1);
        if lean_obj_tag(v_val_3272_) == 1 {
            let mut v_v_3273_: u8 = 0;
            v_v_3273_ = lean_ctor_get_uint8(v_val_3272_, 0 as u32);
            lean_dec_ref_known(v_val_3272_, 0);
            return v_v_3273_;
        } else {
            let mut v___x_3274_: u8 = 0;
            lean_dec(v_val_3272_);
            v___x_3274_ = (lean_unbox(v_defValue_3268_) as u8);
            return v___x_3274_;
        }
    }
}
pub unsafe fn l_Lean_getPPInstantiateMVars___boxed(
    mut v_o_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3276_: u8 = 0;
    let mut v_r_3277_: *mut LeanObject = core::ptr::null_mut();
    v_res_3276_ = l_Lean_getPPInstantiateMVars(v_o_3275_);
    lean_dec_ref(v_o_3275_);
    v_r_3277_ = lean_box((v_res_3276_) as usize);
    return v_r_3277_;
}
pub unsafe fn l_Lean_getPPMVars(mut v_o_3278_: *mut LeanObject) -> u8 {
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3279_ = l_Lean_pp_mvars;
    v_name_3280_ = lean_ctor_get(v___x_3279_, 0);
    v_defValue_3281_ = lean_ctor_get(v___x_3279_, 1);
    v_map_3282_ = lean_ctor_get(v_o_3278_, 0);
    v___x_3283_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3282_,
            v_name_3280_,
        );
    if lean_obj_tag(v___x_3283_) == 0 {
        let mut v___x_3284_: u8 = 0;
        v___x_3284_ = (lean_unbox(v_defValue_3281_) as u8);
        return v___x_3284_;
    } else {
        let mut v_val_3285_: *mut LeanObject = core::ptr::null_mut();
        v_val_3285_ = lean_ctor_get(v___x_3283_, 0);
        lean_inc(v_val_3285_);
        lean_dec_ref_known(v___x_3283_, 1);
        if lean_obj_tag(v_val_3285_) == 1 {
            let mut v_v_3286_: u8 = 0;
            v_v_3286_ = lean_ctor_get_uint8(v_val_3285_, 0 as u32);
            lean_dec_ref_known(v_val_3285_, 0);
            return v_v_3286_;
        } else {
            let mut v___x_3287_: u8 = 0;
            lean_dec(v_val_3285_);
            v___x_3287_ = (lean_unbox(v_defValue_3281_) as u8);
            return v___x_3287_;
        }
    }
}
pub unsafe fn l_Lean_getPPMVars___boxed(mut v_o_3288_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3289_: u8 = 0;
    let mut v_r_3290_: *mut LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_Lean_getPPMVars(v_o_3288_);
    lean_dec_ref(v_o_3288_);
    v_r_3290_ = lean_box((v_res_3289_) as usize);
    return v_r_3290_;
}
pub unsafe fn l_Lean_getPPMVarsAnonymous(mut v_o_3291_: *mut LeanObject) -> u8 {
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3296_: u8 = 0;
    let mut v_map_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3300_: u8 = 0;
    let mut v___x_3301_: u8 = 0;
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3292_ = l_Lean_pp_mvars_anonymous;
                v_name_3293_ = lean_ctor_get(v___x_3292_, 0);
                v_defValue_3294_ = lean_ctor_get(v___x_3292_, 1);
                v___x_3301_ = (lean_unbox(v_defValue_3294_) as u8);
                if v___x_3301_ == 0 {
                    v___x_3302_ = (lean_unbox(v_defValue_3294_) as u8);
                    v___y_3296_ = v___x_3302_;
                    state = 1;
                    continue;
                } else {
                    v___x_3303_ = l_Lean_getPPMVars(v_o_3291_);
                    v___y_3296_ = v___x_3303_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3297_ = lean_ctor_get(v_o_3291_, 0);
                v___x_3298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3297_, v_name_3293_);
                if lean_obj_tag(v___x_3298_) == 0 {
                    return v___y_3296_;
                } else {
                    v_val_3299_ = lean_ctor_get(v___x_3298_, 0);
                    lean_inc(v_val_3299_);
                    lean_dec_ref_known(v___x_3298_, 1);
                    if lean_obj_tag(v_val_3299_) == 1 {
                        v_v_3300_ = lean_ctor_get_uint8(v_val_3299_, 0 as u32);
                        lean_dec_ref_known(v_val_3299_, 0);
                        return v_v_3300_;
                    } else {
                        lean_dec(v_val_3299_);
                        return v___y_3296_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPMVarsAnonymous___boxed(
    mut v_o_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3305_: u8 = 0;
    let mut v_r_3306_: *mut LeanObject = core::ptr::null_mut();
    v_res_3305_ = l_Lean_getPPMVarsAnonymous(v_o_3304_);
    lean_dec_ref(v_o_3304_);
    v_r_3306_ = lean_box((v_res_3305_) as usize);
    return v_r_3306_;
}
pub unsafe fn l_Lean_getPPMVarsLevels(mut v_o_3307_: *mut LeanObject) -> u8 {
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3312_: u8 = 0;
    let mut v_map_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3316_: u8 = 0;
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: u8 = 0;
    let mut v___x_3319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3308_ = l_Lean_pp_mvars_levels;
                v_name_3309_ = lean_ctor_get(v___x_3308_, 0);
                v_defValue_3310_ = lean_ctor_get(v___x_3308_, 1);
                v___x_3317_ = (lean_unbox(v_defValue_3310_) as u8);
                if v___x_3317_ == 0 {
                    v___x_3318_ = (lean_unbox(v_defValue_3310_) as u8);
                    v___y_3312_ = v___x_3318_;
                    state = 1;
                    continue;
                } else {
                    v___x_3319_ = l_Lean_getPPMVarsAnonymous(v_o_3307_);
                    v___y_3312_ = v___x_3319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3313_ = lean_ctor_get(v_o_3307_, 0);
                v___x_3314_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3313_, v_name_3309_);
                if lean_obj_tag(v___x_3314_) == 0 {
                    return v___y_3312_;
                } else {
                    v_val_3315_ = lean_ctor_get(v___x_3314_, 0);
                    lean_inc(v_val_3315_);
                    lean_dec_ref_known(v___x_3314_, 1);
                    if lean_obj_tag(v_val_3315_) == 1 {
                        v_v_3316_ = lean_ctor_get_uint8(v_val_3315_, 0 as u32);
                        lean_dec_ref_known(v_val_3315_, 0);
                        return v_v_3316_;
                    } else {
                        lean_dec(v_val_3315_);
                        return v___y_3312_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPMVarsLevels___boxed(mut v_o_3320_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3321_: u8 = 0;
    let mut v_r_3322_: *mut LeanObject = core::ptr::null_mut();
    v_res_3321_ = l_Lean_getPPMVarsLevels(v_o_3320_);
    lean_dec_ref(v_o_3320_);
    v_r_3322_ = lean_box((v_res_3321_) as usize);
    return v_r_3322_;
}
pub unsafe fn l_Lean_getPPMVarsWithType(mut v_o_3323_: *mut LeanObject) -> u8 {
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Lean_pp_mvars_withType;
    v_name_3325_ = lean_ctor_get(v___x_3324_, 0);
    v_defValue_3326_ = lean_ctor_get(v___x_3324_, 1);
    v_map_3327_ = lean_ctor_get(v_o_3323_, 0);
    v___x_3328_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3327_,
            v_name_3325_,
        );
    if lean_obj_tag(v___x_3328_) == 0 {
        let mut v___x_3329_: u8 = 0;
        v___x_3329_ = (lean_unbox(v_defValue_3326_) as u8);
        return v___x_3329_;
    } else {
        let mut v_val_3330_: *mut LeanObject = core::ptr::null_mut();
        v_val_3330_ = lean_ctor_get(v___x_3328_, 0);
        lean_inc(v_val_3330_);
        lean_dec_ref_known(v___x_3328_, 1);
        if lean_obj_tag(v_val_3330_) == 1 {
            let mut v_v_3331_: u8 = 0;
            v_v_3331_ = lean_ctor_get_uint8(v_val_3330_, 0 as u32);
            lean_dec_ref_known(v_val_3330_, 0);
            return v_v_3331_;
        } else {
            let mut v___x_3332_: u8 = 0;
            lean_dec(v_val_3330_);
            v___x_3332_ = (lean_unbox(v_defValue_3326_) as u8);
            return v___x_3332_;
        }
    }
}
pub unsafe fn l_Lean_getPPMVarsWithType___boxed(mut v_o_3333_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3334_: u8 = 0;
    let mut v_r_3335_: *mut LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_getPPMVarsWithType(v_o_3333_);
    lean_dec_ref(v_o_3333_);
    v_r_3335_ = lean_box((v_res_3334_) as usize);
    return v_r_3335_;
}
pub unsafe fn l_Lean_getPPMVarsDelayed(mut v_o_3336_: *mut LeanObject) -> u8 {
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3341_: u8 = 0;
    let mut v_map_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3345_: u8 = 0;
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3337_ = l_Lean_pp_mvars_delayed;
                v_name_3338_ = lean_ctor_get(v___x_3337_, 0);
                v_defValue_3339_ = lean_ctor_get(v___x_3337_, 1);
                v___x_3346_ = (lean_unbox(v_defValue_3339_) as u8);
                if v___x_3346_ == 0 {
                    v___x_3347_ = l_Lean_getPPAll(v_o_3336_);
                    v___y_3341_ = v___x_3347_;
                    state = 1;
                    continue;
                } else {
                    v___x_3348_ = (lean_unbox(v_defValue_3339_) as u8);
                    v___y_3341_ = v___x_3348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3342_ = lean_ctor_get(v_o_3336_, 0);
                v___x_3343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3342_, v_name_3338_);
                if lean_obj_tag(v___x_3343_) == 0 {
                    return v___y_3341_;
                } else {
                    v_val_3344_ = lean_ctor_get(v___x_3343_, 0);
                    lean_inc(v_val_3344_);
                    lean_dec_ref_known(v___x_3343_, 1);
                    if lean_obj_tag(v_val_3344_) == 1 {
                        v_v_3345_ = lean_ctor_get_uint8(v_val_3344_, 0 as u32);
                        lean_dec_ref_known(v_val_3344_, 0);
                        return v_v_3345_;
                    } else {
                        lean_dec(v_val_3344_);
                        return v___y_3341_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPMVarsDelayed___boxed(mut v_o_3349_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3350_: u8 = 0;
    let mut v_r_3351_: *mut LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_Lean_getPPMVarsDelayed(v_o_3349_);
    lean_dec_ref(v_o_3349_);
    v_r_3351_ = lean_box((v_res_3350_) as usize);
    return v_r_3351_;
}
pub unsafe fn l_Lean_getPPFVarsAnonymous(mut v_o_3352_: *mut LeanObject) -> u8 {
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    v___x_3353_ = l_Lean_pp_fvars_anonymous;
    v_name_3354_ = lean_ctor_get(v___x_3353_, 0);
    v_defValue_3355_ = lean_ctor_get(v___x_3353_, 1);
    v_map_3356_ = lean_ctor_get(v_o_3352_, 0);
    v___x_3357_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3356_,
            v_name_3354_,
        );
    if lean_obj_tag(v___x_3357_) == 0 {
        let mut v___x_3358_: u8 = 0;
        v___x_3358_ = (lean_unbox(v_defValue_3355_) as u8);
        return v___x_3358_;
    } else {
        let mut v_val_3359_: *mut LeanObject = core::ptr::null_mut();
        v_val_3359_ = lean_ctor_get(v___x_3357_, 0);
        lean_inc(v_val_3359_);
        lean_dec_ref_known(v___x_3357_, 1);
        if lean_obj_tag(v_val_3359_) == 1 {
            let mut v_v_3360_: u8 = 0;
            v_v_3360_ = lean_ctor_get_uint8(v_val_3359_, 0 as u32);
            lean_dec_ref_known(v_val_3359_, 0);
            return v_v_3360_;
        } else {
            let mut v___x_3361_: u8 = 0;
            lean_dec(v_val_3359_);
            v___x_3361_ = (lean_unbox(v_defValue_3355_) as u8);
            return v___x_3361_;
        }
    }
}
pub unsafe fn l_Lean_getPPFVarsAnonymous___boxed(
    mut v_o_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3363_: u8 = 0;
    let mut v_r_3364_: *mut LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_getPPFVarsAnonymous(v_o_3362_);
    lean_dec_ref(v_o_3362_);
    v_r_3364_ = lean_box((v_res_3363_) as usize);
    return v_r_3364_;
}
pub unsafe fn l_Lean_getPPBeta(mut v_o_3365_: *mut LeanObject) -> u8 {
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Lean_pp_beta;
    v_name_3367_ = lean_ctor_get(v___x_3366_, 0);
    v_defValue_3368_ = lean_ctor_get(v___x_3366_, 1);
    v_map_3369_ = lean_ctor_get(v_o_3365_, 0);
    v___x_3370_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3369_,
            v_name_3367_,
        );
    if lean_obj_tag(v___x_3370_) == 0 {
        let mut v___x_3371_: u8 = 0;
        v___x_3371_ = (lean_unbox(v_defValue_3368_) as u8);
        return v___x_3371_;
    } else {
        let mut v_val_3372_: *mut LeanObject = core::ptr::null_mut();
        v_val_3372_ = lean_ctor_get(v___x_3370_, 0);
        lean_inc(v_val_3372_);
        lean_dec_ref_known(v___x_3370_, 1);
        if lean_obj_tag(v_val_3372_) == 1 {
            let mut v_v_3373_: u8 = 0;
            v_v_3373_ = lean_ctor_get_uint8(v_val_3372_, 0 as u32);
            lean_dec_ref_known(v_val_3372_, 0);
            return v_v_3373_;
        } else {
            let mut v___x_3374_: u8 = 0;
            lean_dec(v_val_3372_);
            v___x_3374_ = (lean_unbox(v_defValue_3368_) as u8);
            return v___x_3374_;
        }
    }
}
pub unsafe fn l_Lean_getPPBeta___boxed(mut v_o_3375_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3376_: u8 = 0;
    let mut v_r_3377_: *mut LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Lean_getPPBeta(v_o_3375_);
    lean_dec_ref(v_o_3375_);
    v_r_3377_ = lean_box((v_res_3376_) as usize);
    return v_r_3377_;
}
pub unsafe fn l_Lean_getPPSafeShadowing(mut v_o_3378_: *mut LeanObject) -> u8 {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_pp_safeShadowing;
    v_name_3380_ = lean_ctor_get(v___x_3379_, 0);
    v_defValue_3381_ = lean_ctor_get(v___x_3379_, 1);
    v_map_3382_ = lean_ctor_get(v_o_3378_, 0);
    v___x_3383_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3382_,
            v_name_3380_,
        );
    if lean_obj_tag(v___x_3383_) == 0 {
        let mut v___x_3384_: u8 = 0;
        v___x_3384_ = (lean_unbox(v_defValue_3381_) as u8);
        return v___x_3384_;
    } else {
        let mut v_val_3385_: *mut LeanObject = core::ptr::null_mut();
        v_val_3385_ = lean_ctor_get(v___x_3383_, 0);
        lean_inc(v_val_3385_);
        lean_dec_ref_known(v___x_3383_, 1);
        if lean_obj_tag(v_val_3385_) == 1 {
            let mut v_v_3386_: u8 = 0;
            v_v_3386_ = lean_ctor_get_uint8(v_val_3385_, 0 as u32);
            lean_dec_ref_known(v_val_3385_, 0);
            return v_v_3386_;
        } else {
            let mut v___x_3387_: u8 = 0;
            lean_dec(v_val_3385_);
            v___x_3387_ = (lean_unbox(v_defValue_3381_) as u8);
            return v___x_3387_;
        }
    }
}
pub unsafe fn l_Lean_getPPSafeShadowing___boxed(mut v_o_3388_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3389_: u8 = 0;
    let mut v_r_3390_: *mut LeanObject = core::ptr::null_mut();
    v_res_3389_ = l_Lean_getPPSafeShadowing(v_o_3388_);
    lean_dec_ref(v_o_3388_);
    v_r_3390_ = lean_box((v_res_3389_) as usize);
    return v_r_3390_;
}
pub unsafe fn l_Lean_getPPProofs(mut v_o_3391_: *mut LeanObject) -> u8 {
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: u8 = 0;
    let mut v_map_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3400_: u8 = 0;
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3392_ = l_Lean_pp_proofs;
                v_name_3393_ = lean_ctor_get(v___x_3392_, 0);
                v_defValue_3394_ = lean_ctor_get(v___x_3392_, 1);
                v___x_3401_ = (lean_unbox(v_defValue_3394_) as u8);
                if v___x_3401_ == 0 {
                    v___x_3402_ = l_Lean_getPPAll(v_o_3391_);
                    v___y_3396_ = v___x_3402_;
                    state = 1;
                    continue;
                } else {
                    v___x_3403_ = (lean_unbox(v_defValue_3394_) as u8);
                    v___y_3396_ = v___x_3403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3397_ = lean_ctor_get(v_o_3391_, 0);
                v___x_3398_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3397_, v_name_3393_);
                if lean_obj_tag(v___x_3398_) == 0 {
                    return v___y_3396_;
                } else {
                    v_val_3399_ = lean_ctor_get(v___x_3398_, 0);
                    lean_inc(v_val_3399_);
                    lean_dec_ref_known(v___x_3398_, 1);
                    if lean_obj_tag(v_val_3399_) == 1 {
                        v_v_3400_ = lean_ctor_get_uint8(v_val_3399_, 0 as u32);
                        lean_dec_ref_known(v_val_3399_, 0);
                        return v_v_3400_;
                    } else {
                        lean_dec(v_val_3399_);
                        return v___y_3396_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPProofs___boxed(mut v_o_3404_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3405_: u8 = 0;
    let mut v_r_3406_: *mut LeanObject = core::ptr::null_mut();
    v_res_3405_ = l_Lean_getPPProofs(v_o_3404_);
    lean_dec_ref(v_o_3404_);
    v_r_3406_ = lean_box((v_res_3405_) as usize);
    return v_r_3406_;
}
pub unsafe fn l_Lean_getPPProofsWithType(mut v_o_3407_: *mut LeanObject) -> u8 {
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    v___x_3408_ = l_Lean_pp_proofs_withType;
    v_name_3409_ = lean_ctor_get(v___x_3408_, 0);
    v_defValue_3410_ = lean_ctor_get(v___x_3408_, 1);
    v_map_3411_ = lean_ctor_get(v_o_3407_, 0);
    v___x_3412_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3411_,
            v_name_3409_,
        );
    if lean_obj_tag(v___x_3412_) == 0 {
        let mut v___x_3413_: u8 = 0;
        v___x_3413_ = (lean_unbox(v_defValue_3410_) as u8);
        return v___x_3413_;
    } else {
        let mut v_val_3414_: *mut LeanObject = core::ptr::null_mut();
        v_val_3414_ = lean_ctor_get(v___x_3412_, 0);
        lean_inc(v_val_3414_);
        lean_dec_ref_known(v___x_3412_, 1);
        if lean_obj_tag(v_val_3414_) == 1 {
            let mut v_v_3415_: u8 = 0;
            v_v_3415_ = lean_ctor_get_uint8(v_val_3414_, 0 as u32);
            lean_dec_ref_known(v_val_3414_, 0);
            return v_v_3415_;
        } else {
            let mut v___x_3416_: u8 = 0;
            lean_dec(v_val_3414_);
            v___x_3416_ = (lean_unbox(v_defValue_3410_) as u8);
            return v___x_3416_;
        }
    }
}
pub unsafe fn l_Lean_getPPProofsWithType___boxed(
    mut v_o_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3418_: u8 = 0;
    let mut v_r_3419_: *mut LeanObject = core::ptr::null_mut();
    v_res_3418_ = l_Lean_getPPProofsWithType(v_o_3417_);
    lean_dec_ref(v_o_3417_);
    v_r_3419_ = lean_box((v_res_3418_) as usize);
    return v_r_3419_;
}
pub unsafe fn l_Lean_getPPProofsThreshold(mut v_o_3420_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    v___x_3421_ = l_Lean_pp_proofs_threshold;
    v_name_3422_ = lean_ctor_get(v___x_3421_, 0);
    v_defValue_3423_ = lean_ctor_get(v___x_3421_, 1);
    v_map_3424_ = lean_ctor_get(v_o_3420_, 0);
    v___x_3425_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3424_,
            v_name_3422_,
        );
    if lean_obj_tag(v___x_3425_) == 0 {
        lean_inc(v_defValue_3423_);
        return v_defValue_3423_;
    } else {
        let mut v_val_3426_: *mut LeanObject = core::ptr::null_mut();
        v_val_3426_ = lean_ctor_get(v___x_3425_, 0);
        lean_inc(v_val_3426_);
        lean_dec_ref_known(v___x_3425_, 1);
        if lean_obj_tag(v_val_3426_) == 3 {
            let mut v_v_3427_: *mut LeanObject = core::ptr::null_mut();
            v_v_3427_ = lean_ctor_get(v_val_3426_, 0);
            lean_inc(v_v_3427_);
            lean_dec_ref_known(v_val_3426_, 1);
            return v_v_3427_;
        } else {
            lean_dec(v_val_3426_);
            lean_inc(v_defValue_3423_);
            return v_defValue_3423_;
        }
    }
}
pub unsafe fn l_Lean_getPPProofsThreshold___boxed(
    mut v_o_3428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3429_: *mut LeanObject = core::ptr::null_mut();
    v_res_3429_ = l_Lean_getPPProofsThreshold(v_o_3428_);
    lean_dec_ref(v_o_3428_);
    return v_res_3429_;
}
pub unsafe fn l_Lean_getPPMotivesPi(mut v_o_3430_: *mut LeanObject) -> u8 {
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3431_ = l_Lean_pp_motives_pi;
    v_name_3432_ = lean_ctor_get(v___x_3431_, 0);
    v_defValue_3433_ = lean_ctor_get(v___x_3431_, 1);
    v_map_3434_ = lean_ctor_get(v_o_3430_, 0);
    v___x_3435_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3434_,
            v_name_3432_,
        );
    if lean_obj_tag(v___x_3435_) == 0 {
        let mut v___x_3436_: u8 = 0;
        v___x_3436_ = (lean_unbox(v_defValue_3433_) as u8);
        return v___x_3436_;
    } else {
        let mut v_val_3437_: *mut LeanObject = core::ptr::null_mut();
        v_val_3437_ = lean_ctor_get(v___x_3435_, 0);
        lean_inc(v_val_3437_);
        lean_dec_ref_known(v___x_3435_, 1);
        if lean_obj_tag(v_val_3437_) == 1 {
            let mut v_v_3438_: u8 = 0;
            v_v_3438_ = lean_ctor_get_uint8(v_val_3437_, 0 as u32);
            lean_dec_ref_known(v_val_3437_, 0);
            return v_v_3438_;
        } else {
            let mut v___x_3439_: u8 = 0;
            lean_dec(v_val_3437_);
            v___x_3439_ = (lean_unbox(v_defValue_3433_) as u8);
            return v___x_3439_;
        }
    }
}
pub unsafe fn l_Lean_getPPMotivesPi___boxed(mut v_o_3440_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3441_: u8 = 0;
    let mut v_r_3442_: *mut LeanObject = core::ptr::null_mut();
    v_res_3441_ = l_Lean_getPPMotivesPi(v_o_3440_);
    lean_dec_ref(v_o_3440_);
    v_r_3442_ = lean_box((v_res_3441_) as usize);
    return v_r_3442_;
}
pub unsafe fn l_Lean_getPPMotivesNonConst(mut v_o_3443_: *mut LeanObject) -> u8 {
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_pp_motives_nonConst;
    v_name_3445_ = lean_ctor_get(v___x_3444_, 0);
    v_defValue_3446_ = lean_ctor_get(v___x_3444_, 1);
    v_map_3447_ = lean_ctor_get(v_o_3443_, 0);
    v___x_3448_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3447_,
            v_name_3445_,
        );
    if lean_obj_tag(v___x_3448_) == 0 {
        let mut v___x_3449_: u8 = 0;
        v___x_3449_ = (lean_unbox(v_defValue_3446_) as u8);
        return v___x_3449_;
    } else {
        let mut v_val_3450_: *mut LeanObject = core::ptr::null_mut();
        v_val_3450_ = lean_ctor_get(v___x_3448_, 0);
        lean_inc(v_val_3450_);
        lean_dec_ref_known(v___x_3448_, 1);
        if lean_obj_tag(v_val_3450_) == 1 {
            let mut v_v_3451_: u8 = 0;
            v_v_3451_ = lean_ctor_get_uint8(v_val_3450_, 0 as u32);
            lean_dec_ref_known(v_val_3450_, 0);
            return v_v_3451_;
        } else {
            let mut v___x_3452_: u8 = 0;
            lean_dec(v_val_3450_);
            v___x_3452_ = (lean_unbox(v_defValue_3446_) as u8);
            return v___x_3452_;
        }
    }
}
pub unsafe fn l_Lean_getPPMotivesNonConst___boxed(
    mut v_o_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3454_: u8 = 0;
    let mut v_r_3455_: *mut LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Lean_getPPMotivesNonConst(v_o_3453_);
    lean_dec_ref(v_o_3453_);
    v_r_3455_ = lean_box((v_res_3454_) as usize);
    return v_r_3455_;
}
pub unsafe fn l_Lean_getPPMotivesAll(mut v_o_3456_: *mut LeanObject) -> u8 {
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    v___x_3457_ = l_Lean_pp_motives_all;
    v_name_3458_ = lean_ctor_get(v___x_3457_, 0);
    v_defValue_3459_ = lean_ctor_get(v___x_3457_, 1);
    v_map_3460_ = lean_ctor_get(v_o_3456_, 0);
    v___x_3461_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3460_,
            v_name_3458_,
        );
    if lean_obj_tag(v___x_3461_) == 0 {
        let mut v___x_3462_: u8 = 0;
        v___x_3462_ = (lean_unbox(v_defValue_3459_) as u8);
        return v___x_3462_;
    } else {
        let mut v_val_3463_: *mut LeanObject = core::ptr::null_mut();
        v_val_3463_ = lean_ctor_get(v___x_3461_, 0);
        lean_inc(v_val_3463_);
        lean_dec_ref_known(v___x_3461_, 1);
        if lean_obj_tag(v_val_3463_) == 1 {
            let mut v_v_3464_: u8 = 0;
            v_v_3464_ = lean_ctor_get_uint8(v_val_3463_, 0 as u32);
            lean_dec_ref_known(v_val_3463_, 0);
            return v_v_3464_;
        } else {
            let mut v___x_3465_: u8 = 0;
            lean_dec(v_val_3463_);
            v___x_3465_ = (lean_unbox(v_defValue_3459_) as u8);
            return v___x_3465_;
        }
    }
}
pub unsafe fn l_Lean_getPPMotivesAll___boxed(mut v_o_3466_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3467_: u8 = 0;
    let mut v_r_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Lean_getPPMotivesAll(v_o_3466_);
    lean_dec_ref(v_o_3466_);
    v_r_3468_ = lean_box((v_res_3467_) as usize);
    return v_r_3468_;
}
pub unsafe fn l_Lean_getPPInstances(mut v_o_3469_: *mut LeanObject) -> u8 {
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    v___x_3470_ = l_Lean_pp_instances;
    v_name_3471_ = lean_ctor_get(v___x_3470_, 0);
    v_defValue_3472_ = lean_ctor_get(v___x_3470_, 1);
    v_map_3473_ = lean_ctor_get(v_o_3469_, 0);
    v___x_3474_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3473_,
            v_name_3471_,
        );
    if lean_obj_tag(v___x_3474_) == 0 {
        let mut v___x_3475_: u8 = 0;
        v___x_3475_ = (lean_unbox(v_defValue_3472_) as u8);
        return v___x_3475_;
    } else {
        let mut v_val_3476_: *mut LeanObject = core::ptr::null_mut();
        v_val_3476_ = lean_ctor_get(v___x_3474_, 0);
        lean_inc(v_val_3476_);
        lean_dec_ref_known(v___x_3474_, 1);
        if lean_obj_tag(v_val_3476_) == 1 {
            let mut v_v_3477_: u8 = 0;
            v_v_3477_ = lean_ctor_get_uint8(v_val_3476_, 0 as u32);
            lean_dec_ref_known(v_val_3476_, 0);
            return v_v_3477_;
        } else {
            let mut v___x_3478_: u8 = 0;
            lean_dec(v_val_3476_);
            v___x_3478_ = (lean_unbox(v_defValue_3472_) as u8);
            return v___x_3478_;
        }
    }
}
pub unsafe fn l_Lean_getPPInstances___boxed(mut v_o_3479_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3480_: u8 = 0;
    let mut v_r_3481_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Lean_getPPInstances(v_o_3479_);
    lean_dec_ref(v_o_3479_);
    v_r_3481_ = lean_box((v_res_3480_) as usize);
    return v_r_3481_;
}
pub unsafe fn l_Lean_getPPInstanceTypes(mut v_o_3482_: *mut LeanObject) -> u8 {
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_pp_instanceTypes;
    v_name_3484_ = lean_ctor_get(v___x_3483_, 0);
    v_defValue_3485_ = lean_ctor_get(v___x_3483_, 1);
    v_map_3486_ = lean_ctor_get(v_o_3482_, 0);
    v___x_3487_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3486_,
            v_name_3484_,
        );
    if lean_obj_tag(v___x_3487_) == 0 {
        let mut v___x_3488_: u8 = 0;
        v___x_3488_ = (lean_unbox(v_defValue_3485_) as u8);
        return v___x_3488_;
    } else {
        let mut v_val_3489_: *mut LeanObject = core::ptr::null_mut();
        v_val_3489_ = lean_ctor_get(v___x_3487_, 0);
        lean_inc(v_val_3489_);
        lean_dec_ref_known(v___x_3487_, 1);
        if lean_obj_tag(v_val_3489_) == 1 {
            let mut v_v_3490_: u8 = 0;
            v_v_3490_ = lean_ctor_get_uint8(v_val_3489_, 0 as u32);
            lean_dec_ref_known(v_val_3489_, 0);
            return v_v_3490_;
        } else {
            let mut v___x_3491_: u8 = 0;
            lean_dec(v_val_3489_);
            v___x_3491_ = (lean_unbox(v_defValue_3485_) as u8);
            return v___x_3491_;
        }
    }
}
pub unsafe fn l_Lean_getPPInstanceTypes___boxed(mut v_o_3492_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3493_: u8 = 0;
    let mut v_r_3494_: *mut LeanObject = core::ptr::null_mut();
    v_res_3493_ = l_Lean_getPPInstanceTypes(v_o_3492_);
    lean_dec_ref(v_o_3492_);
    v_r_3494_ = lean_box((v_res_3493_) as usize);
    return v_r_3494_;
}
pub unsafe fn l_Lean_getPPDeepTerms(mut v_o_3495_: *mut LeanObject) -> u8 {
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3500_: u8 = 0;
    let mut v_map_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3504_: u8 = 0;
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ = l_Lean_pp_deepTerms;
                v_name_3497_ = lean_ctor_get(v___x_3496_, 0);
                v_defValue_3498_ = lean_ctor_get(v___x_3496_, 1);
                v___x_3505_ = (lean_unbox(v_defValue_3498_) as u8);
                if v___x_3505_ == 0 {
                    v___x_3506_ = l_Lean_getPPAll(v_o_3495_);
                    v___y_3500_ = v___x_3506_;
                    state = 1;
                    continue;
                } else {
                    v___x_3507_ = (lean_unbox(v_defValue_3498_) as u8);
                    v___y_3500_ = v___x_3507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_3501_ = lean_ctor_get(v_o_3495_, 0);
                v___x_3502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3501_, v_name_3497_);
                if lean_obj_tag(v___x_3502_) == 0 {
                    return v___y_3500_;
                } else {
                    v_val_3503_ = lean_ctor_get(v___x_3502_, 0);
                    lean_inc(v_val_3503_);
                    lean_dec_ref_known(v___x_3502_, 1);
                    if lean_obj_tag(v_val_3503_) == 1 {
                        v_v_3504_ = lean_ctor_get_uint8(v_val_3503_, 0 as u32);
                        lean_dec_ref_known(v_val_3503_, 0);
                        return v_v_3504_;
                    } else {
                        lean_dec(v_val_3503_);
                        return v___y_3500_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getPPDeepTerms___boxed(mut v_o_3508_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3509_: u8 = 0;
    let mut v_r_3510_: *mut LeanObject = core::ptr::null_mut();
    v_res_3509_ = l_Lean_getPPDeepTerms(v_o_3508_);
    lean_dec_ref(v_o_3508_);
    v_r_3510_ = lean_box((v_res_3509_) as usize);
    return v_r_3510_;
}
pub unsafe fn l_Lean_getPPDeepTermsThreshold(mut v_o_3511_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    v___x_3512_ = l_Lean_pp_deepTerms_threshold;
    v_name_3513_ = lean_ctor_get(v___x_3512_, 0);
    v_defValue_3514_ = lean_ctor_get(v___x_3512_, 1);
    v_map_3515_ = lean_ctor_get(v_o_3511_, 0);
    v___x_3516_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3515_,
            v_name_3513_,
        );
    if lean_obj_tag(v___x_3516_) == 0 {
        lean_inc(v_defValue_3514_);
        return v_defValue_3514_;
    } else {
        let mut v_val_3517_: *mut LeanObject = core::ptr::null_mut();
        v_val_3517_ = lean_ctor_get(v___x_3516_, 0);
        lean_inc(v_val_3517_);
        lean_dec_ref_known(v___x_3516_, 1);
        if lean_obj_tag(v_val_3517_) == 3 {
            let mut v_v_3518_: *mut LeanObject = core::ptr::null_mut();
            v_v_3518_ = lean_ctor_get(v_val_3517_, 0);
            lean_inc(v_v_3518_);
            lean_dec_ref_known(v_val_3517_, 1);
            return v_v_3518_;
        } else {
            lean_dec(v_val_3517_);
            lean_inc(v_defValue_3514_);
            return v_defValue_3514_;
        }
    }
}
pub unsafe fn l_Lean_getPPDeepTermsThreshold___boxed(
    mut v_o_3519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3520_: *mut LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Lean_getPPDeepTermsThreshold(v_o_3519_);
    lean_dec_ref(v_o_3519_);
    return v_res_3520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4080382135____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_maxSteps = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_maxSteps);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2147881510____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_all = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_all);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3540906103____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_notation = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_notation);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2924075583____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_parens = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_parens);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_41206397____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_unicode = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_unicode);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_238768327____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_unicode_fun = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_unicode_fun);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3406008996____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_match = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_match);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1900330263____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_sorrySource = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_sorrySource);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_141571828____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_coercions = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_coercions);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2458050899____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_coercions_types = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_coercions_types);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1378879936____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_universes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_universes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2604662143____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_fullNames = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_fullNames);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3140146471____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_privateNames = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_privateNames);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_697692632____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_funBinderTypes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_funBinderTypes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3322021038____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_piBinderTypes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_piBinderTypes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1652516111____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_piBinderNames = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_piBinderNames);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_218093965____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_piBinderNames_hygienic = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_piBinderNames_hygienic);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3638865395____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_foralls = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_foralls);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_565042913____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_letVarTypes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_letVarTypes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1352222462____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_natLit = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_natLit);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1240114214____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_numericTypes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_numericTypes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1325818894____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_mdata = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_mdata);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2248579234____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_instantiateMVars = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_instantiateMVars);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2409783491____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_mvars = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_mvars);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_406403817____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_mvars_levels = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_mvars_levels);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1488711282____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_mvars_anonymous = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_mvars_anonymous);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1250207126____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_mvars_withType = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_mvars_withType);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1210529748____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_mvars_delayed = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_mvars_delayed);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2308334303____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_fvars_anonymous = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_fvars_anonymous);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_547122284____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_beta = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_beta);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_343083742____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_structureInstances = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_structureInstances);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1368066901____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_structureInstances_flatten = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_structureInstances_flatten);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2070467515____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_structureInstances_defaults = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_structureInstances_defaults);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3525746343____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_fieldNotation = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_fieldNotation);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1807480764____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_fieldNotation_generalized = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_fieldNotation_generalized);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_74134663____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_explicit = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_explicit);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2610318467____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_structureInstanceTypes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_structureInstanceTypes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_714017495____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_safeShadowing = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_safeShadowing);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_4108030048____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_tagAppFns = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_tagAppFns);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_760538935____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_proofs = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_proofs);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2268496730____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_proofs_withType = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_proofs_withType);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1672848969____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_proofs_threshold = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_proofs_threshold);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3524043324____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_instances = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_instances);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_2232209702____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_instanceTypes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_instanceTypes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_750911636____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_deepTerms = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_deepTerms);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1327993095____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_deepTerms_threshold = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_deepTerms_threshold);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3077001566____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_motives_pi = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_motives_pi);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_3637927591____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_motives_nonConst = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_motives_nonConst);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Delaborator_Options_0__Lean_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Options_1858164116____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_motives_all = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_motives_all);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_Options(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
}
