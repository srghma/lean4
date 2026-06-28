// Lean compiler output
// Module: Lean.Compiler.Options
// Imports: Lean.Util.Trace
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Util::Trace::{
    initialize_Lean_Util_Trace, runtime_initialize_Lean_Util_Trace,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_tag, lean_unbox,
};
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,6769370416094023508 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [116, 121, 112, 101, 32, 99, 104, 101, 99, 107, 32, 99, 111, 100, 101, 32, 97, 102, 116, 101, 114, 32, 101, 97, 99, 104, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 115, 116, 101, 112, 32, 40, 116, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 112, 117, 114, 115, 101, 115, 41, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11491352321210023419 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 114, 97, 99, 101, 85, 110, 110, 111, 114, 109, 97, 108, 105, 122, 101, 100, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject,11237630579005899553 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value: LeanStringObject<111> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 110, m_data: [100, 111, 110, 39, 116, 32, 110, 111, 114, 109, 97, 108, 105, 122, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 98, 101, 102, 111, 114, 101, 32, 116, 114, 97, 99, 105, 110, 103, 32, 116, 104, 101, 109, 32, 97, 116, 32, 101, 97, 99, 104, 32, 112, 105, 112, 101, 108, 105, 110, 101, 32, 115, 116, 101, 112, 32, 40, 116, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 112, 117, 114, 112, 111, 115, 101, 115, 41, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject,15021673321254255310 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 104, 101, 99, 107, 77, 101, 116, 97, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject,8726745013164009300 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value: LeanStringObject<217> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 217, m_capacity: 217, m_length: 216, m_data: [67, 104, 101, 99, 107, 32, 116, 104, 97, 116, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 111, 110, 108, 121, 32, 114, 101, 102, 101, 114, 32, 116, 111, 32, 111, 116, 104, 101, 114, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 100, 105, 116, 116, 111, 32, 102, 111, 114, 32, 110, 111, 110, 45, 96, 109, 101, 116, 97, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 46, 32, 68, 105, 115, 97, 98, 108, 105, 110, 103, 32, 116, 104, 105, 115, 32, 111, 112, 116, 105, 111, 110, 32, 109, 97, 121, 32, 108, 101, 97, 100, 32, 116, 111, 32, 100, 101, 108, 97, 121, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 101, 114, 114, 111, 114, 115, 32, 97, 110, 100, 32, 105, 115, 10, 32, 32, 32, 32, 105, 110, 116, 101, 110, 100, 101, 100, 32, 111, 110, 108, 121, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 112, 117, 114, 112, 111, 115, 101, 115, 46, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject,11345753305454106107 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 101, 108, 97, 120, 101, 100, 77, 101, 116, 97, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject,15378060581612458978 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value: LeanStringObject<99> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 99, m_capacity: 99, m_length: 98, m_data: [65, 108, 108, 111, 119, 32, 109, 105, 120, 101, 100, 32, 96, 109, 101, 116, 97, 96, 47, 110, 111, 110, 45, 96, 109, 101, 116, 97, 96, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 115, 32, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 109, 111, 100, 117, 108, 101, 46, 32, 82, 101, 102, 101, 114, 101, 110, 99, 101, 115, 32, 116, 111, 32, 105, 109, 112, 111, 114, 116, 115, 32, 97, 114, 101, 32, 117, 110, 97, 102, 102, 101, 99, 116, 101, 100, 46, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject,6438068985958529125 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [105, 103, 110, 111, 114, 101, 66, 111, 114, 114, 111, 119, 65, 110, 110, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject,8572073003005844426 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value: LeanStringObject<104> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [73, 103, 110, 111, 114, 101, 32, 117, 115, 101, 114, 32, 100, 101, 102, 105, 110, 101, 100, 32, 98, 111, 114, 114, 111, 119, 32, 105, 110, 102, 101, 114, 101, 110, 99, 101, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 101, 120, 112, 111, 114, 116, 47, 101, 120, 116, 101, 114, 110, 32, 102, 111, 114, 119, 97, 114, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject,984169368689992733 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [112, 111, 115, 116, 112, 111, 110, 101, 67, 111, 109, 112, 105, 108, 101, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject,4054798134254680491 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value: LeanStringObject<61> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 46, 32, 84, 111, 103, 103, 108, 101, 32, 101, 120, 112, 101, 114, 105, 109, 101, 110, 116, 97, 108, 32, 96, 108, 101, 97, 110, 105, 114, 96, 32, 115, 101, 112, 97, 114, 97, 116, 101, 32, 99, 111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject,11052568782285477252 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 76, 101, 97, 110, 73, 82, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject,13742365252871709065 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 46, 32, 73, 110, 100, 105, 99, 97, 116, 101, 115, 32, 119, 104, 101, 116, 104, 101, 114, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 105, 115, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 114, 117, 110, 110, 105, 110, 103, 32, 105, 110, 32, 96, 108, 101, 97, 110, 105, 114, 96, 46, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,9249165468102354002 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject,16068216535330913542 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 112, 114, 101, 116, 101, 114, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 101, 102, 101, 114, 95, 110, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject,15543695762065283380 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject,2643107538822917897 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [40, 105, 110, 116, 101, 114, 112, 114, 101, 116, 101, 114, 41, 32, 119, 104, 101, 116, 104, 101, 114, 32, 116, 111, 32, 117, 115, 101, 32, 112, 114, 101, 99, 111, 109, 112, 105, 108, 101, 100, 32, 99, 111, 100, 101, 32, 119, 104, 101, 114, 101, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject,11592378953522143031 as *mut LeanObject] };
pub static l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject,16752613177018548894 as *mut LeanObject] };
static mut l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4__value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(
    mut v_name_214_: *mut LeanObject,
    mut v_decl_215_: *mut LeanObject,
    mut v_ref_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: u8 = 0;
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_227_: u8 = 0;
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_unused_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_237_: u8 = 0;
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_218_ = lean_ctor_get(v_decl_215_, 0);
                v_descr_219_ = lean_ctor_get(v_decl_215_, 1);
                v_deprecation_x3f_220_ = lean_ctor_get(v_decl_215_, 2);
                v___x_221_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_222_ = (lean_unbox(v_defValue_218_) as u8);
                lean_ctor_set_uint8(v___x_221_, 0 as u32, v___x_222_);
                lean_inc(v_deprecation_x3f_220_);
                lean_inc_ref(v_descr_219_);
                lean_inc_n(v_name_214_, 2);
                v___x_223_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_223_, 0, v_name_214_);
                lean_ctor_set(v___x_223_, 1, v_ref_216_);
                lean_ctor_set(v___x_223_, 2, v___x_221_);
                lean_ctor_set(v___x_223_, 3, v_descr_219_);
                lean_ctor_set(v___x_223_, 4, v_deprecation_x3f_220_);
                v___x_224_ = lean_register_option(v_name_214_, v___x_223_);
                if lean_obj_tag(v___x_224_) == 0 {
                    v_isSharedCheck_232_ = (!lean_is_exclusive(v___x_224_)) as u8;
                    if v_isSharedCheck_232_ == 0 {
                        v_unused_233_ = lean_ctor_get(v___x_224_, 0);
                        lean_dec(v_unused_233_);
                        v___x_226_ = v___x_224_;
                        v_isShared_227_ = v_isSharedCheck_232_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_224_);
                        v___x_226_ = lean_box(0);
                        v_isShared_227_ = v_isSharedCheck_232_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_214_);
                    v_a_234_ = lean_ctor_get(v___x_224_, 0);
                    v_isSharedCheck_241_ = (!lean_is_exclusive(v___x_224_)) as u8;
                    if v_isSharedCheck_241_ == 0 {
                        v___x_236_ = v___x_224_;
                        v_isShared_237_ = v_isSharedCheck_241_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_234_);
                        lean_dec(v___x_224_);
                        v___x_236_ = lean_box(0);
                        v_isShared_237_ = v_isSharedCheck_241_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_218_);
                v___x_228_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_228_, 0, v_name_214_);
                lean_ctor_set(v___x_228_, 1, v_defValue_218_);
                if v_isShared_227_ == 0 {
                    lean_ctor_set(v___x_226_, 0, v___x_228_);
                    v___x_230_ = v___x_226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
                    v___x_230_ = v_reuseFailAlloc_231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_230_;
            }
            3 => {
                if v_isShared_237_ == 0 {
                    v___x_239_ = v___x_236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
                    v___x_239_ = v_reuseFailAlloc_240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_242_: *mut LeanObject,
    mut v_decl_243_: *mut LeanObject,
    mut v_ref_244_: *mut LeanObject,
    mut v_a_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_246_: *mut LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v_name_242_, v_decl_243_, v_ref_244_);
    lean_dec_ref(v_decl_243_);
    return v_res_246_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
    v___x_267_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
    v___x_268_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_;
    v___x_269_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_266_, v___x_267_, v___x_268_);
    return v___x_269_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(
    mut v_a_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_271_: *mut LeanObject = core::ptr::null_mut();
    v_res_271_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
    return v_res_271_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_288_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_;
    v___x_289_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_;
    v___x_290_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_;
    v___x_291_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_288_, v___x_289_, v___x_290_);
    return v___x_291_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4____boxed(
    mut v_a_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_293_: *mut LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
    return v_res_293_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    v___x_310_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
    v___x_311_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
    v___x_312_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_;
    v___x_313_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_310_, v___x_311_, v___x_312_);
    return v___x_313_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(
    mut v_a_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_315_: *mut LeanObject = core::ptr::null_mut();
    v_res_315_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
    return v_res_315_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_;
    v___x_333_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_;
    v___x_334_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_;
    v___x_335_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_332_, v___x_333_, v___x_334_);
    return v___x_335_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4____boxed(
    mut v_a_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_res_337_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
    return v_res_337_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v___x_354_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_;
    v___x_355_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_;
    v___x_356_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_;
    v___x_357_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_354_, v___x_355_, v___x_356_);
    return v___x_357_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4____boxed(
    mut v_a_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_359_: *mut LeanObject = core::ptr::null_mut();
    v_res_359_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
    return v_res_359_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_;
    v___x_377_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_;
    v___x_378_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_;
    v___x_379_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_376_, v___x_377_, v___x_378_);
    return v___x_379_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4____boxed(
    mut v_a_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_381_: *mut LeanObject = core::ptr::null_mut();
    v_res_381_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
    return v_res_381_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_;
    v___x_399_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_;
    v___x_400_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_;
    v___x_401_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_398_, v___x_399_, v___x_400_);
    return v___x_401_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4____boxed(
    mut v_a_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_403_: *mut LeanObject = core::ptr::null_mut();
    v_res_403_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
    return v_res_403_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_421_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_;
    v___x_422_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_;
    v___x_423_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_;
    v___x_424_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_421_, v___x_422_, v___x_423_);
    return v___x_424_;
}
pub unsafe fn l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4____boxed(
    mut v_a_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_426_: *mut LeanObject = core::ptr::null_mut();
    v_res_426_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_();
    return v_res_426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_check);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_traceUnnormalized = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_traceUnnormalized);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_checkMeta = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_checkMeta);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_relaxedMetaCheck = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_relaxedMetaCheck);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_ignoreBorrowAnnotation = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_ignoreBorrowAnnotation);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_postponeCompile = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_postponeCompile);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_compiler_inLeanIR = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_compiler_inLeanIR);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3040012986____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_interpreter_prefer__native = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_interpreter_prefer__native);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_Options(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_Options(builtin);
}
