// Lean compiler output
// Module: Lean.Meta.Match
// Imports: Lean.Meta.Match.MatchPatternAttr Lean.Meta.Match.Match Lean.Meta.Match.CaseValues Lean.Meta.Match.CaseArraySizes Lean.Meta.Match.MatchEqs
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Match::CaseArraySizes::{
    initialize_Lean_Meta_Match_CaseArraySizes, runtime_initialize_Lean_Meta_Match_CaseArraySizes,
};
use crate::r#gen::Lean::Meta::Match::CaseValues::{
    initialize_Lean_Meta_Match_CaseValues, runtime_initialize_Lean_Meta_Match_CaseValues,
};
use crate::r#gen::Lean::Meta::Match::Match::{
    initialize_Lean_Meta_Match_Match, runtime_initialize_Lean_Meta_Match_Match,
};
use crate::r#gen::Lean::Meta::Match::MatchEqs::{
    initialize_Lean_Meta_Match_MatchEqs, runtime_initialize_Lean_Meta_Match_MatchEqs,
};
use crate::r#gen::Lean::Meta::Match::MatchPatternAttr::{
    initialize_Lean_Meta_Match_MatchPatternAttr,
    runtime_initialize_Lean_Meta_Match_MatchPatternAttr,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Match_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17634115403684839930 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4282541520667412299 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,1160174257927099702 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6846268447976695903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15441783407473675134 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5977727482305805983 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14285650698600955986 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8962737844521118406 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10947672935338714259 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = leanh::lean_unsigned_to_nat(3442551600);
    v___x_107_ = l___private_Lean_Meta_Match_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_;
    v___x_108_ = l_Lean_Name_num___override(v___x_107_, v___x_106_);
    return v___x_108_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_110_ = l___private_Lean_Meta_Match_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_;
    v___x_111_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_);
    v___x_112_ = l_Lean_Name_str___override(v___x_111_, v___x_110_);
    return v___x_112_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_114_ = l___private_Lean_Meta_Match_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_;
    v___x_115_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_);
    v___x_116_ = l_Lean_Name_str___override(v___x_115_, v___x_114_);
    return v___x_116_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_117_ = leanh::lean_unsigned_to_nat(2);
    v___x_118_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_);
    v___x_119_ = l_Lean_Name_num___override(v___x_118_, v___x_117_);
    return v___x_119_;
}
pub unsafe fn l___private_Lean_Meta_Match_0__Lean_initFn_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_121_ = l___private_Lean_Meta_Match_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_;
    v___x_122_ = 0;
    v___x_123_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_);
    v___x_124_ = l_Lean_registerTraceClass(v___x_121_, v___x_122_, v___x_123_);
    return v___x_124_;
}
pub unsafe fn l___private_Lean_Meta_Match_0__Lean_initFn_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2____boxed(
    mut v_a_125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_126_ = l___private_Lean_Meta_Match_0__Lean_initFn_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_();
    return v_res_126_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Match(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_CaseValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatchEqs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Match_0__Lean_initFn_00___x40_Lean_Meta_Match_3442551600____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_Match(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_CaseValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_CaseArraySizes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatchEqs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match(builtin);
}