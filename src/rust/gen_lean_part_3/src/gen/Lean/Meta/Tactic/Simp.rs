// Lean compiler output
// Module: Lean.Meta.Tactic.Simp
// Imports: Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Simp.SimpAll Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs Lean.Meta.Tactic.Simp.RegisterCommand Lean.Meta.Tactic.Simp.Attr Lean.Meta.Tactic.Simp.Diagnostics Lean.Meta.Tactic.Simp.Arith
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::{
    initialize_Lean_Meta_Tactic_Simp_Arith, runtime_initialize_Lean_Meta_Tactic_Simp_Arith,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::{
    initialize_Lean_Meta_Tactic_Simp_Attr, runtime_initialize_Lean_Meta_Tactic_Simp_Attr,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Diagnostics::{
    initialize_Lean_Meta_Tactic_Simp_Diagnostics,
    runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::RegisterCommand::{
    initialize_Lean_Meta_Tactic_Simp_RegisterCommand,
    runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::{
    initialize_Lean_Meta_Tactic_Simp_Rewrite, runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpAll::{
    initialize_Lean_Meta_Tactic_Simp_SimpAll, runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::{
    initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems,
    runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    initialize_Lean_Meta_Tactic_Simp_SimpTheorems,
    runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12926315994152569291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1610795400267900086 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,584435734957338079 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9064935220242579198 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9324758380921299487 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15260838037368170962 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5658330884295705158 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8740229618984457435 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11271822109882725331 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1719608285 as usize) << 1) | 1) as *mut leanh::LeanObject,12334303077373713356 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13583981193957649731 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11495071738509432931 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,10771723870413210470 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12613902607223922729 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 115, 99, 104, 97, 114, 103, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1639065281199068809 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1097110872 as usize) << 1) | 1) as *mut leanh::LeanObject,11066683055541650583 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6030909120239425436 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,121712094412507752 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,14084422713142732585 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 119, 114, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5302717395259495988 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1156789139 as usize) << 1) | 1) as *mut leanh::LeanObject,4514615251134351537 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13042503758709194194 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7459608768660074494 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,16024616073545679055 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 68, 101, 102, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10151709650713276005 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 110, 105, 102, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11740398936186061502 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1418113237 as usize) << 1) | 1) as *mut leanh::LeanObject,13875069269882589840 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2385602218760808455 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8704668259268958287 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,7637145980851913482 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 114, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,447171421563751857 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 793727544 as usize) << 1) | 1) as *mut leanh::LeanObject,6069281596842392015 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11646191467470420612 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7117634824079269904 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,5081367102781024385 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 111, 111, 112, 80, 114, 111, 116, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11537002108020701424 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 768544759 as usize) << 1) | 1) as *mut leanh::LeanObject,376220942534501061 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1927080958614729558 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4663476802470391082 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,8854757241812841491 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 117, 109, 83, 116, 101, 112, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13762269513032256163 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 581839081 as usize) << 1) | 1) as *mut leanh::LeanObject,13537812070110975824 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12450095028725553351 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18112471455795326351 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,12038285344707207498 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 97, 100, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4639420730068104075 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 888696210 as usize) << 1) | 1) as *mut leanh::LeanObject,8200073909186823921 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17471232207915027730 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7928192827165694654 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,12836432602049651343 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject,976856721057904807 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11531678945225641079 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9556918813098452982 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14987375182540660802 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 337957312 as usize) << 1) | 1) as *mut leanh::LeanObject,7561472338793161610 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4501457717698184837 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2334075456013239717 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,7728685168459784232 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value) as *mut leanh::LeanObject,976856721057904807 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11531678945225641079 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9556918813098452982 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14987375182540660802 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9808280626460866485 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_414_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_415_ = 0;
    v___x_416_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_417_ = l_Lean_registerTraceClass(v___x_414_, v___x_415_, v___x_416_);
    return v___x_417_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2____boxed(
    mut v_a_418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_419_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_();
    return v_res_419_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_426_ = leanh::lean_unsigned_to_nat(3870689133);
    v___x_427_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_428_ = l_Lean_Name_num___override(v___x_427_, v___x_426_);
    return v___x_428_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_430_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
    v___x_431_ = l_Lean_Name_str___override(v___x_430_, v___x_429_);
    return v___x_431_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_433_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
    v___x_434_ = l_Lean_Name_str___override(v___x_433_, v___x_432_);
    return v___x_434_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = leanh::lean_unsigned_to_nat(2);
    v___x_436_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
    v___x_437_ = l_Lean_Name_num___override(v___x_436_, v___x_435_);
    return v___x_437_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: u8 = 0;
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_;
    v___x_440_ = 1;
    v___x_441_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
    v___x_442_ = l_Lean_registerTraceClass(v___x_439_, v___x_440_, v___x_441_);
    return v___x_442_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2____boxed(
    mut v_a_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_444_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_();
    return v_res_444_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_;
    v___x_465_ = 1;
    v___x_466_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_;
    v___x_467_ = l_Lean_registerTraceClass(v___x_464_, v___x_465_, v___x_466_);
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2____boxed(
    mut v_a_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_469_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_();
    return v_res_469_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_;
    v___x_490_ = 1;
    v___x_491_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_;
    v___x_492_ = l_Lean_registerTraceClass(v___x_489_, v___x_490_, v___x_491_);
    return v___x_492_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2____boxed(
    mut v_a_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_();
    return v_res_494_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_501_ = leanh::lean_unsigned_to_nat(4009644764);
    v___x_502_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_503_ = l_Lean_Name_num___override(v___x_502_, v___x_501_);
    return v___x_503_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_505_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
    v___x_506_ = l_Lean_Name_str___override(v___x_505_, v___x_504_);
    return v___x_506_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_507_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_508_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
    v___x_509_ = l_Lean_Name_str___override(v___x_508_, v___x_507_);
    return v___x_509_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = leanh::lean_unsigned_to_nat(2);
    v___x_511_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
    v___x_512_ = l_Lean_Name_num___override(v___x_511_, v___x_510_);
    return v___x_512_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_;
    v___x_515_ = 1;
    v___x_516_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
    v___x_517_ = l_Lean_registerTraceClass(v___x_514_, v___x_515_, v___x_516_);
    return v___x_517_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2____boxed(
    mut v_a_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_();
    return v_res_519_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_539_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_;
    v___x_540_ = 1;
    v___x_541_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_;
    v___x_542_ = l_Lean_registerTraceClass(v___x_539_, v___x_540_, v___x_541_);
    return v___x_542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2____boxed(
    mut v_a_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_544_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_();
    return v_res_544_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_;
    v___x_565_ = 1;
    v___x_566_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_;
    v___x_567_ = l_Lean_registerTraceClass(v___x_564_, v___x_565_, v___x_566_);
    return v___x_567_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2____boxed(
    mut v_a_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_569_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_();
    return v_res_569_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_;
    v___x_590_ = 1;
    v___x_591_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_;
    v___x_592_ = l_Lean_registerTraceClass(v___x_589_, v___x_590_, v___x_591_);
    return v___x_592_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2____boxed(
    mut v_a_593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_594_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_();
    return v_res_594_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_;
    v___x_615_ = 0;
    v___x_616_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_;
    v___x_617_ = l_Lean_registerTraceClass(v___x_614_, v___x_615_, v___x_616_);
    return v___x_617_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2____boxed(
    mut v_a_618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_619_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_();
    return v_res_619_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u8 = 0;
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_;
    v___x_640_ = 0;
    v___x_641_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_;
    v___x_642_ = l_Lean_registerTraceClass(v___x_639_, v___x_640_, v___x_641_);
    return v___x_642_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2____boxed(
    mut v_a_643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_644_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_();
    return v_res_644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: u8 = 0;
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_;
    v___x_665_ = 0;
    v___x_666_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_;
    v___x_667_ = l_Lean_registerTraceClass(v___x_664_, v___x_665_, v___x_666_);
    return v___x_667_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2____boxed(
    mut v_a_668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_();
    return v_res_669_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = leanh::lean_unsigned_to_nat(2225316046);
    v___x_677_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_678_ = l_Lean_Name_num___override(v___x_677_, v___x_676_);
    return v___x_678_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_680_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
    v___x_681_ = l_Lean_Name_str___override(v___x_680_, v___x_679_);
    return v___x_681_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_;
    v___x_683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
    v___x_684_ = l_Lean_Name_str___override(v___x_683_, v___x_682_);
    return v___x_684_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ = leanh::lean_unsigned_to_nat(2);
    v___x_686_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
    v___x_687_ = l_Lean_Name_num___override(v___x_686_, v___x_685_);
    return v___x_687_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_;
    v___x_690_ = 1;
    v___x_691_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
    v___x_692_ = l_Lean_registerTraceClass(v___x_689_, v___x_690_, v___x_691_);
    return v___x_692_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2____boxed(
    mut v_a_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_();
    return v_res_694_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp(builtin);
}