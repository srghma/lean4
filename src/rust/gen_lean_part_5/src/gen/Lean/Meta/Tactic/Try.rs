// Lean compiler output
// Module: Lean.Meta.Tactic.Try
// Imports: Lean.Meta.Tactic.Try.Collect
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Tactic::Try::Collect::{
    initialize_Lean_Meta_Tactic_Try_Collect, runtime_initialize_Lean_Meta_Tactic_Try_Collect,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,827222806734303871 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [84, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13219314582965609519 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,14957110057256732482 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17808984058641298595 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5474232068195740034 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3598159099569124235 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5982899312081524982 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7141080140909888594 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6759024670652990935 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13165935561703201843 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 108, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,827222806734303871 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1795265806735138497 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 381124472 as usize) << 1) | 1) as *mut leanh::LeanObject,11267141968218927240 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6330933496807014063 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9579340776541237271 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,13541794636633652162 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 117, 110, 73, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,827222806734303871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1795265806735138497 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15769919125638983832 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,827222806734303871 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15732359656535989308 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 103928808 as usize) << 1) | 1) as *mut leanh::LeanObject,1823376177210569297 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2622814942604987954 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5105051062602943582 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,8022160743641598447 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,827222806734303871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15732359656535989308 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9301335154374427049 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 104, 97, 105, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,827222806734303871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15732359656535989308 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13344127349705853389 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_237_ = leanh::lean_unsigned_to_nat(2909380237);
    v___x_238_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_239_ = l_Lean_Name_num___override(v___x_238_, v___x_237_);
    return v___x_239_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_242_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
    v___x_243_ = l_Lean_Name_str___override(v___x_242_, v___x_241_);
    return v___x_243_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_245_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_246_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
    v___x_247_ = l_Lean_Name_str___override(v___x_246_, v___x_245_);
    return v___x_247_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_248_ = leanh::lean_unsigned_to_nat(2);
    v___x_249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
    v___x_250_ = l_Lean_Name_num___override(v___x_249_, v___x_248_);
    return v___x_250_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: u8 = 0;
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_253_ = 0;
    v___x_254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
    v___x_255_ = l_Lean_registerTraceClass(v___x_252_, v___x_253_, v___x_254_);
    return v___x_255_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2____boxed(
    mut v_a_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
    return v_res_257_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: u8 = 0;
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_275_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_;
    v___x_276_ = 0;
    v___x_277_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_;
    v___x_278_ = l_Lean_registerTraceClass(v___x_275_, v___x_276_, v___x_277_);
    return v___x_278_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2____boxed(
    mut v_a_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_280_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
    return v_res_280_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_286_ = leanh::lean_unsigned_to_nat(3813147919);
    v___x_287_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_288_ = l_Lean_Name_num___override(v___x_287_, v___x_286_);
    return v___x_288_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
    v___x_291_ = l_Lean_Name_str___override(v___x_290_, v___x_289_);
    return v___x_291_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_293_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
    v___x_294_ = l_Lean_Name_str___override(v___x_293_, v___x_292_);
    return v___x_294_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = leanh::lean_unsigned_to_nat(2);
    v___x_296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
    v___x_297_ = l_Lean_Name_num___override(v___x_296_, v___x_295_);
    return v___x_297_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: u8 = 0;
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_;
    v___x_300_ = 0;
    v___x_301_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
    v___x_302_ = l_Lean_registerTraceClass(v___x_299_, v___x_300_, v___x_301_);
    return v___x_302_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2____boxed(
    mut v_a_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
    return v_res_304_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: u8 = 0;
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_;
    v___x_323_ = 0;
    v___x_324_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_;
    v___x_325_ = l_Lean_registerTraceClass(v___x_322_, v___x_323_, v___x_324_);
    return v___x_325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2____boxed(
    mut v_a_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_327_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
    return v_res_327_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = leanh::lean_unsigned_to_nat(2260799134);
    v___x_333_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_334_ = l_Lean_Name_num___override(v___x_333_, v___x_332_);
    return v___x_334_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_336_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
    v___x_337_ = l_Lean_Name_str___override(v___x_336_, v___x_335_);
    return v___x_337_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
    v___x_340_ = l_Lean_Name_str___override(v___x_339_, v___x_338_);
    return v___x_340_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = leanh::lean_unsigned_to_nat(2);
    v___x_342_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
    v___x_343_ = l_Lean_Name_num___override(v___x_342_, v___x_341_);
    return v___x_343_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: u8 = 0;
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_;
    v___x_346_ = 0;
    v___x_347_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
    v___x_348_ = l_Lean_registerTraceClass(v___x_345_, v___x_346_, v___x_347_);
    return v___x_348_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2____boxed(
    mut v_a_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
    return v_res_350_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = leanh::lean_unsigned_to_nat(2306426978);
    v___x_357_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_358_ = l_Lean_Name_num___override(v___x_357_, v___x_356_);
    return v___x_358_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_360_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
    v___x_361_ = l_Lean_Name_str___override(v___x_360_, v___x_359_);
    return v___x_361_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
    v___x_363_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
    v___x_364_ = l_Lean_Name_str___override(v___x_363_, v___x_362_);
    return v___x_364_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = leanh::lean_unsigned_to_nat(2);
    v___x_366_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
    v___x_367_ = l_Lean_Name_num___override(v___x_366_, v___x_365_);
    return v___x_367_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: u8 = 0;
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_;
    v___x_370_ = 0;
    v___x_371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
    v___x_372_ = l_Lean_registerTraceClass(v___x_369_, v___x_370_, v___x_371_);
    return v___x_372_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2____boxed(
    mut v_a_373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_374_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
    return v_res_374_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Try(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Try_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Try(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Try(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Try_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Try(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Try(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Try(builtin);
}