// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv
// Imports: Lean.Meta.Tactic.Cbv.Main Lean.Meta.Tactic.Cbv.Util Lean.Meta.Tactic.Cbv.CbvEvalExt
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Tactic::Cbv::CbvEvalExt::{
    initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt, runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::Main::{
    initialize_Lean_Meta_Tactic_Cbv_Main, runtime_initialize_Lean_Meta_Tactic_Cbv_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::Util::{
    initialize_Lean_Meta_Tactic_Cbv_Util, runtime_initialize_Lean_Meta_Tactic_Cbv_Util,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9691683737394756276 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16489734963670585437 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,2533875570721614184 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2946661493469489857 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9490207456622729336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1460363104240831689 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14857985846996285452 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14585505261883861808 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9121072691139032141 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17241200210543731379 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 119, 114, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9691683737394756276 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15200645332484307630 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1674345266 as usize) << 1) | 1) as *mut leanh::LeanObject,5282223889092634983 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8723029179803127564 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2813532942792077624 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,10586736713015692857 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9691683737394756276 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9984592913233547682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1090948466 as usize) << 1) | 1) as *mut leanh::LeanObject,7929075819637697090 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8351130312163788269 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,661414522285105325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,5345665145060739712 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 116, 114, 111, 108, 70, 108, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9691683737394756276 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject,957843270380816252 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1675791195 as usize) << 1) | 1) as *mut leanh::LeanObject,5902108885385472818 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15682923783954065853 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10127042422274695325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,16500395125217433200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 114, 111, 99, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9691683737394756276 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1605478173386622269 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value) as *mut leanh::LeanObject,976856721057904807 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11531678945225641079 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9556918813098452982 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6255161424381068048 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value) as *mut leanh::LeanObject,976856721057904807 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11531678945225641079 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9556918813098452982 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6255161424381068048 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3982922405713416392 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_275_ = leanh::lean_unsigned_to_nat(4268171306);
    v___x_276_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_277_ = l_Lean_Name_num___override(v___x_276_, v___x_275_);
    return v___x_277_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_279_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_280_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
    v___x_281_ = l_Lean_Name_str___override(v___x_280_, v___x_279_);
    return v___x_281_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
    v___x_285_ = l_Lean_Name_str___override(v___x_284_, v___x_283_);
    return v___x_285_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_286_ = leanh::lean_unsigned_to_nat(2);
    v___x_287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
    v___x_288_ = l_Lean_Name_num___override(v___x_287_, v___x_286_);
    return v___x_288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: u8 = 0;
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_291_ = 0;
    v___x_292_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
    v___x_293_ = l_Lean_registerTraceClass(v___x_290_, v___x_291_, v___x_292_);
    return v___x_293_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2____boxed(
    mut v_a_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_();
    return v_res_295_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: u8 = 0;
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_;
    v___x_316_ = 1;
    v___x_317_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_;
    v___x_318_ = l_Lean_registerTraceClass(v___x_315_, v___x_316_, v___x_317_);
    return v___x_318_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2____boxed(
    mut v_a_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_();
    return v_res_320_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: u8 = 0;
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_;
    v___x_341_ = 1;
    v___x_342_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_;
    v___x_343_ = l_Lean_registerTraceClass(v___x_340_, v___x_341_, v___x_342_);
    return v___x_343_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2____boxed(
    mut v_a_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_();
    return v_res_345_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: u8 = 0;
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_;
    v___x_366_ = 1;
    v___x_367_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_;
    v___x_368_ = l_Lean_registerTraceClass(v___x_365_, v___x_366_, v___x_367_);
    return v___x_368_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2____boxed(
    mut v_a_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_370_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_();
    return v_res_370_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_unsigned_to_nat(3053287543);
    v___x_378_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_379_ = l_Lean_Name_num___override(v___x_378_, v___x_377_);
    return v___x_379_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_381_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
    v___x_382_ = l_Lean_Name_str___override(v___x_381_, v___x_380_);
    return v___x_382_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
    v___x_385_ = l_Lean_Name_str___override(v___x_384_, v___x_383_);
    return v___x_385_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_386_ = leanh::lean_unsigned_to_nat(2);
    v___x_387_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
    v___x_388_ = l_Lean_Name_num___override(v___x_387_, v___x_386_);
    return v___x_388_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: u8 = 0;
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_;
    v___x_391_ = 1;
    v___x_392_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
    v___x_393_ = l_Lean_registerTraceClass(v___x_390_, v___x_391_, v___x_392_);
    return v___x_393_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2____boxed(
    mut v_a_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_();
    return v_res_395_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = leanh::lean_unsigned_to_nat(2526460641);
    v___x_403_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_404_ = l_Lean_Name_num___override(v___x_403_, v___x_402_);
    return v___x_404_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_406_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
    v___x_407_ = l_Lean_Name_str___override(v___x_406_, v___x_405_);
    return v___x_407_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_408_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_409_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
    v___x_410_ = l_Lean_Name_str___override(v___x_409_, v___x_408_);
    return v___x_410_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = leanh::lean_unsigned_to_nat(2);
    v___x_412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
    v___x_413_ = l_Lean_Name_num___override(v___x_412_, v___x_411_);
    return v___x_413_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: u8 = 0;
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_;
    v___x_416_ = 0;
    v___x_417_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
    v___x_418_ = l_Lean_registerTraceClass(v___x_415_, v___x_416_, v___x_417_);
    return v___x_418_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2____boxed(
    mut v_a_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
    return v_res_420_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = leanh::lean_unsigned_to_nat(4273416105);
    v___x_429_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_430_ = l_Lean_Name_num___override(v___x_429_, v___x_428_);
    return v___x_430_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_432_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
    v___x_433_ = l_Lean_Name_str___override(v___x_432_, v___x_431_);
    return v___x_433_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
    v___x_435_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
    v___x_436_ = l_Lean_Name_str___override(v___x_435_, v___x_434_);
    return v___x_436_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ = leanh::lean_unsigned_to_nat(2);
    v___x_438_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
    v___x_439_ = l_Lean_Name_num___override(v___x_438_, v___x_437_);
    return v___x_439_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_;
    v___x_442_ = 1;
    v___x_443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
    v___x_444_ = l_Lean_registerTraceClass(v___x_441_, v___x_442_, v___x_443_);
    return v___x_444_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2____boxed(
    mut v_a_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_446_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_();
    return v_res_446_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv(builtin);
}