// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order
// Imports: Lean.Meta.Tactic.Grind.Order.Types Lean.Meta.Tactic.Grind.Order.Internalize Lean.Meta.Tactic.Grind.Order.StructId Lean.Meta.Tactic.Grind.Order.OrderM Lean.Meta.Tactic.Grind.Order.Assert Lean.Meta.Tactic.Grind.Order.Util
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::Assert::{
    initialize_Lean_Meta_Tactic_Grind_Order_Assert, l_Lean_Meta_Grind_Order_processNewEq___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::Internalize::{
    initialize_Lean_Meta_Tactic_Grind_Order_Internalize,
    l_Lean_Meta_Grind_Order_internalize___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_Internalize,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::OrderM::{
    initialize_Lean_Meta_Tactic_Grind_Order_OrderM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::StructId::{
    initialize_Lean_Meta_Tactic_Grind_Order_StructId,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::Types::{
    initialize_Lean_Meta_Tactic_Grind_Order_Types, l_Lean_Meta_Grind_Order_orderExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::Util::{
    initialize_Lean_Meta_Tactic_Grind_Order_Util,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_SolverExtension_setMethods___redArg;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_11, lean_box, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,8034346934164294440 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,622053547050603573 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,2169041216295121600 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,3697875489546077561 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,2568147641782072284 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,12886948615998491168 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,18438057128186597610 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,6503682093190101003 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,5178668491143738298 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,7738068439606239795 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,11621239771198125598 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,4439679018671470346 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,9427677052487032863 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,13338815588117955649 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,13946787064321355716 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,8034346934164294440 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject,17756122566391284854 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 344686027 as usize) << 1) | 1) as *mut LeanObject,13326289358116068240 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,17561661280798430471 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,1816361510570598223 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,9125414128160118282 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,8034346934164294440 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject,9805036161735487433 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 563761110 as usize) << 1) | 1) as *mut LeanObject,8676749831116430724 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,4489727066661612203 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,7512828909657944683 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,4609906089353058494 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,8034346934164294440 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value) as *mut LeanObject,9805036161735487433 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject,5526400292735412161 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 413082279 as usize) << 1) | 1) as *mut LeanObject,6440046725414856215 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15392223581473069084 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15946903078996573928 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,5271033120816657833 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,14560564577775875687 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 907713757 as usize) << 1) | 1) as *mut LeanObject,13098348604418504128 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15510005402442674583 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15992539639547976831 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,14464728396795215290 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 100, 100, 95, 101, 100, 103, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,14560564577775875687 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value) as *mut LeanObject,9819192345984871633 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 114, 111, 112, 97, 103, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,14560564577775875687 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value) as *mut LeanObject,948387691234733198 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 104, 101, 99, 107, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,14560564577775875687 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject,7918387025437057002 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 185970682 as usize) << 1) | 1) as *mut LeanObject,1602820385507950416 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,17482459232499142855 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15789329724680406415 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,6235288787679107402 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [99, 104, 101, 99, 107, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,14560564577775875687 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject,9231607432349732412 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,((( 673264261 as usize) << 1) | 1) as *mut LeanObject,18415725275707308586 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,12433740593771573605 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value) as *mut LeanObject,18314314481685030277 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,14702674130173424328 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Order_internalize___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Order_processNewEq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ = lean_unsigned_to_nat(3007973156);
    v___x_485_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_486_ = l_Lean_Name_num___override(v___x_485_, v___x_484_);
    return v___x_486_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_489_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
    v___x_490_ = l_Lean_Name_str___override(v___x_489_, v___x_488_);
    return v___x_490_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_493_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
    v___x_494_ = l_Lean_Name_str___override(v___x_493_, v___x_492_);
    return v___x_494_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ = lean_unsigned_to_nat(2);
    v___x_496_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
    v___x_497_ = l_Lean_Name_num___override(v___x_496_, v___x_495_);
    return v___x_497_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_500_ = 0;
    v___x_501_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
    v___x_502_ = l_Lean_registerTraceClass(v___x_499_, v___x_500_, v___x_501_);
    return v___x_502_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2____boxed(
    mut v_a_503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_504_: *mut LeanObject = core::ptr::null_mut();
    v_res_504_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
    return v_res_504_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: u8 = 0;
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_523_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_;
    v___x_524_ = 0;
    v___x_525_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_;
    v___x_526_ = l_Lean_registerTraceClass(v___x_523_, v___x_524_, v___x_525_);
    return v___x_526_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2____boxed(
    mut v_a_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_528_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
    return v_res_528_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    v___x_547_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_;
    v___x_548_ = 0;
    v___x_549_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_;
    v___x_550_ = l_Lean_registerTraceClass(v___x_547_, v___x_548_, v___x_549_);
    return v___x_550_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2____boxed(
    mut v_a_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_552_: *mut LeanObject = core::ptr::null_mut();
    v_res_552_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
    return v_res_552_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: u8 = 0;
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    v___x_572_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_;
    v___x_573_ = 0;
    v___x_574_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_;
    v___x_575_ = l_Lean_registerTraceClass(v___x_572_, v___x_573_, v___x_574_);
    return v___x_575_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2____boxed(
    mut v_a_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_577_: *mut LeanObject = core::ptr::null_mut();
    v_res_577_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
    return v_res_577_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_596_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_;
    v___x_597_ = 0;
    v___x_598_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_;
    v___x_599_ = l_Lean_registerTraceClass(v___x_596_, v___x_597_, v___x_598_);
    return v___x_599_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2____boxed(
    mut v_a_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_601_: *mut LeanObject = core::ptr::null_mut();
    v_res_601_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
    return v_res_601_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_unsigned_to_nat(3999496204);
    v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_610_ = l_Lean_Name_num___override(v___x_609_, v___x_608_);
    return v___x_610_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v___x_611_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_612_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
    v___x_613_ = l_Lean_Name_str___override(v___x_612_, v___x_611_);
    return v___x_613_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    v___x_614_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_615_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
    v___x_616_ = l_Lean_Name_str___override(v___x_615_, v___x_614_);
    return v___x_616_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    v___x_617_ = lean_unsigned_to_nat(2);
    v___x_618_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
    v___x_619_ = l_Lean_Name_num___override(v___x_618_, v___x_617_);
    return v___x_619_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    v___x_621_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_;
    v___x_622_ = 1;
    v___x_623_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
    v___x_624_ = l_Lean_registerTraceClass(v___x_621_, v___x_622_, v___x_623_);
    return v___x_624_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2____boxed(
    mut v_a_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_626_: *mut LeanObject = core::ptr::null_mut();
    v_res_626_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
    return v_res_626_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    v___x_633_ = lean_unsigned_to_nat(3855794043);
    v___x_634_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_635_ = l_Lean_Name_num___override(v___x_634_, v___x_633_);
    return v___x_635_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_636_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_637_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
    v___x_638_ = l_Lean_Name_str___override(v___x_637_, v___x_636_);
    return v___x_638_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
    v___x_640_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
    v___x_641_ = l_Lean_Name_str___override(v___x_640_, v___x_639_);
    return v___x_641_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    v___x_642_ = lean_unsigned_to_nat(2);
    v___x_643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
    v___x_644_ = l_Lean_Name_num___override(v___x_643_, v___x_642_);
    return v___x_644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_;
    v___x_647_ = 1;
    v___x_648_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
    v___x_649_ = l_Lean_registerTraceClass(v___x_646_, v___x_647_, v___x_648_);
    return v___x_649_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2____boxed(
    mut v_a_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_651_: *mut LeanObject = core::ptr::null_mut();
    v_res_651_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
    return v_res_651_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    v___x_671_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_;
    v___x_672_ = 1;
    v___x_673_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_;
    v___x_674_ = l_Lean_registerTraceClass(v___x_671_, v___x_672_, v___x_673_);
    return v___x_674_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2____boxed(
    mut v_a_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_676_: *mut LeanObject = core::ptr::null_mut();
    v_res_676_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
    return v_res_676_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_;
    v___x_697_ = 1;
    v___x_698_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_;
    v___x_699_ = l_Lean_registerTraceClass(v___x_696_, v___x_697_, v___x_698_);
    return v___x_699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2____boxed(
    mut v_a_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_701_: *mut LeanObject = core::ptr::null_mut();
    v_res_701_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
    return v_res_701_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(
    mut v_x_702_: *mut LeanObject,
    mut v_x_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
    mut v___y_708_: *mut LeanObject,
    mut v___y_709_: *mut LeanObject,
    mut v___y_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
    mut v___y_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = lean_box(0);
    v___x_716_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_716_, 0, v___x_715_);
    return v___x_716_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(
    mut v_x_717_: *mut LeanObject,
    mut v_x_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
    mut v___y_720_: *mut LeanObject,
    mut v___y_721_: *mut LeanObject,
    mut v___y_722_: *mut LeanObject,
    mut v___y_723_: *mut LeanObject,
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
    mut v___y_726_: *mut LeanObject,
    mut v___y_727_: *mut LeanObject,
    mut v___y_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_730_: *mut LeanObject = core::ptr::null_mut();
    v_res_730_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v_x_717_, v_x_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
    lean_dec(v___y_728_);
    lean_dec_ref(v___y_727_);
    lean_dec(v___y_726_);
    lean_dec_ref(v___y_725_);
    lean_dec(v___y_724_);
    lean_dec_ref(v___y_723_);
    lean_dec(v___y_722_);
    lean_dec_ref(v___y_721_);
    lean_dec(v___y_720_);
    lean_dec(v___y_719_);
    lean_dec_ref(v_x_718_);
    lean_dec_ref(v_x_717_);
    return v_res_730_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
    mut v___y_741_: *mut LeanObject,
    mut v___y_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = lean_apply_11(
        v___y_732_,
        v___y_731_,
        v___y_734_,
        v___y_735_,
        v___y_736_,
        v___y_737_,
        v___y_738_,
        v___y_739_,
        v___y_740_,
        v___y_741_,
        v___y_742_,
        lean_box(0),
    );
    return v___x_744_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
    mut v___y_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
    mut v___y_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_758_: *mut LeanObject = core::ptr::null_mut();
    v_res_758_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
    lean_dec_ref(v___y_747_);
    return v_res_758_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(
    mut v___x_759_: u8,
    mut v___y_760_: *mut LeanObject,
    mut v___y_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = lean_box((v___x_759_) as usize);
    v___x_772_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_772_, 0, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(
    mut v___x_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
    mut v___y_777_: *mut LeanObject,
    mut v___y_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
    mut v___y_780_: *mut LeanObject,
    mut v___y_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1363__boxed_785_: u8 = 0;
    let mut v_res_786_: *mut LeanObject = core::ptr::null_mut();
    v___x_1363__boxed_785_ = (lean_unbox(v___x_773_) as u8);
    v_res_786_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___x_1363__boxed_785_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
    lean_dec(v___y_783_);
    lean_dec_ref(v___y_782_);
    lean_dec(v___y_781_);
    lean_dec_ref(v___y_780_);
    lean_dec(v___y_779_);
    lean_dec_ref(v___y_778_);
    lean_dec(v___y_777_);
    lean_dec_ref(v___y_776_);
    lean_dec(v___y_775_);
    lean_dec(v___y_774_);
    return v_res_786_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(
    mut v___x_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
    mut v___y_789_: *mut LeanObject,
    mut v___y_790_: *mut LeanObject,
    mut v___y_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
    mut v___y_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
    mut v___y_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_799_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_799_, 0, v___x_787_);
    return v___x_799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(
    mut v___x_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
    mut v___y_802_: *mut LeanObject,
    mut v___y_803_: *mut LeanObject,
    mut v___y_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
    lean_dec(v___y_810_);
    lean_dec_ref(v___y_809_);
    lean_dec(v___y_808_);
    lean_dec_ref(v___y_807_);
    lean_dec(v___y_806_);
    lean_dec_ref(v___y_805_);
    lean_dec(v___y_804_);
    lean_dec_ref(v___y_803_);
    lean_dec(v___y_802_);
    lean_dec(v___y_801_);
    return v_res_812_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    v___f_823_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
    v___f_824_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
    v___x_825_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_826_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
    v___x_827_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
    v___f_828_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
    v___f_829_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
    v___x_830_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(
        v___x_825_, v___x_826_, v___x_827_, v___f_823_, v___f_828_, v___f_824_, v___f_828_,
        v___f_829_,
    );
    return v___x_830_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(
    mut v_a_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_832_: *mut LeanObject = core::ptr::null_mut();
    v_res_832_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
    return v_res_832_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order(builtin);
}
