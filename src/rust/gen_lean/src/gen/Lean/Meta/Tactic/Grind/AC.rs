// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC
// Imports: Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Tactic.Grind.AC.Util Lean.Meta.Tactic.Grind.AC.Var Lean.Meta.Tactic.Grind.AC.Internalize Lean.Meta.Tactic.Grind.AC.Eq Lean.Meta.Tactic.Grind.AC.Seq Lean.Meta.Tactic.Grind.AC.Proof Lean.Meta.Tactic.Grind.AC.DenoteExpr Lean.Meta.Tactic.Grind.AC.ToExpr Lean.Meta.Tactic.Grind.AC.VarRename Lean.Meta.Tactic.Grind.AC.PP Lean.Meta.Tactic.Grind.AC.Inv Lean.Meta.Tactic.Grind.AC.Action
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Action::{
    initialize_Lean_Meta_Tactic_Grind_AC_Action, l_Lean_Meta_Grind_Action_ac___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Eq::{
    initialize_Lean_Meta_Tactic_Grind_AC_Eq, l_Lean_Meta_Grind_AC_check_x27___boxed,
    l_Lean_Meta_Grind_AC_processNewDiseq___boxed, l_Lean_Meta_Grind_AC_processNewEq___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Eq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Internalize::{
    initialize_Lean_Meta_Tactic_Grind_AC_Internalize, l_Lean_Meta_Grind_AC_internalize___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Inv::{
    initialize_Lean_Meta_Tactic_Grind_AC_Inv, l_Lean_Meta_Grind_AC_checkInvariants___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::PP::{
    initialize_Lean_Meta_Tactic_Grind_AC_PP, runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Proof::{
    initialize_Lean_Meta_Tactic_Grind_AC_Proof, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Seq::{
    initialize_Lean_Meta_Tactic_Grind_AC_Seq, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::ToExpr::{
    initialize_Lean_Meta_Tactic_Grind_AC_ToExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Types::{
    initialize_Lean_Meta_Tactic_Grind_AC_Types, l_Lean_Meta_Grind_AC_acExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Util::{
    initialize_Lean_Meta_Tactic_Grind_AC_Util, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Var::{
    initialize_Lean_Meta_Tactic_Grind_AC_Var, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_AC_VarRename,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_SolverExtension_setMethods___redArg;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,879949681028799497 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,622053547050603573 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [65, 67, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9833679720422092130 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,10876492392961209027 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5449267603903126670 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11370101394900597978 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13329818882805135512 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13813061580968839619 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13772878334758177442 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3653021379887957291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10747102401205828374 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,464332128530586802 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16445083990711768567 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11527424153304376889 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,226417459394325774 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,879949681028799497 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17125407081629120939 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 728928005 as usize) << 1) | 1) as *mut leanh::LeanObject,11666479823258647805 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7937798241296570558 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6485451413186826034 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,1684588828636210187 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,879949681028799497 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4658627966637684372 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2063561435 as usize) << 1) | 1) as *mut leanh::LeanObject,13923996942334032350 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1197416895326259913 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5006562216204838753 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,9207474267980786492 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,879949681028799497 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3054998659839832757 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15368431810600006387 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1142390893 as usize) << 1) | 1) as *mut leanh::LeanObject,2946909581518095582 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4206782879734569417 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4013633286682163297 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,15028748872595656764 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16654945813534725306 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4557908892501224383 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [113, 117, 101, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6419132828840734896 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1839863265 as usize) << 1) | 1) as *mut leanh::LeanObject,136138189467197185 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14100591488240122690 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6185798942893675726 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,4512015072446472991 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 117, 112, 101, 114, 112, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4797378606001882065 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject,355509172022841795 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1601100932 as usize) << 1) | 1) as *mut leanh::LeanObject,14064649748534264569 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8269459046326146154 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16042667008150620950 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,11667042701216783447 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_AC_internalize___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_AC_processNewEq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_AC_processNewDiseq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_ac___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_AC_check_x27___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_AC_checkInvariants___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = leanh::lean_unsigned_to_nat(3214356224);
    v___x_429_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_430_ = l_Lean_Name_num___override(v___x_429_, v___x_428_);
    return v___x_430_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_433_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
    v___x_434_ = l_Lean_Name_str___override(v___x_433_, v___x_432_);
    return v___x_434_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_437_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
    v___x_438_ = l_Lean_Name_str___override(v___x_437_, v___x_436_);
    return v___x_438_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = leanh::lean_unsigned_to_nat(2);
    v___x_440_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
    v___x_441_ = l_Lean_Name_num___override(v___x_440_, v___x_439_);
    return v___x_441_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_444_ = 0;
    v___x_445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
    v___x_446_ = l_Lean_registerTraceClass(v___x_443_, v___x_444_, v___x_445_);
    return v___x_446_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2____boxed(
    mut v_a_447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
    return v_res_448_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_;
    v___x_468_ = 0;
    v___x_469_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_;
    v___x_470_ = l_Lean_registerTraceClass(v___x_467_, v___x_468_, v___x_469_);
    return v___x_470_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2____boxed(
    mut v_a_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_472_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
    return v_res_472_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_491_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_;
    v___x_492_ = 0;
    v___x_493_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_;
    v___x_494_ = l_Lean_registerTraceClass(v___x_491_, v___x_492_, v___x_493_);
    return v___x_494_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2____boxed(
    mut v_a_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
    return v_res_496_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = leanh::lean_unsigned_to_nat(3749149120);
    v___x_503_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_504_ = l_Lean_Name_num___override(v___x_503_, v___x_502_);
    return v___x_504_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_505_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_506_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
    v___x_507_ = l_Lean_Name_str___override(v___x_506_, v___x_505_);
    return v___x_507_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_509_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
    v___x_510_ = l_Lean_Name_str___override(v___x_509_, v___x_508_);
    return v___x_510_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = leanh::lean_unsigned_to_nat(2);
    v___x_512_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
    v___x_513_ = l_Lean_Name_num___override(v___x_512_, v___x_511_);
    return v___x_513_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_515_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
    v___x_516_ = 0;
    v___x_517_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
    v___x_518_ = l_Lean_registerTraceClass(v___x_515_, v___x_516_, v___x_517_);
    return v___x_518_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2____boxed(
    mut v_a_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
    return v_res_520_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: u8 = 0;
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_;
    v___x_542_ = 0;
    v___x_543_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_;
    v___x_544_ = l_Lean_registerTraceClass(v___x_541_, v___x_542_, v___x_543_);
    return v___x_544_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2____boxed(
    mut v_a_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
    return v_res_546_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = leanh::lean_unsigned_to_nat(4001898889);
    v___x_554_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_555_ = l_Lean_Name_num___override(v___x_554_, v___x_553_);
    return v___x_555_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
    v___x_558_ = l_Lean_Name_str___override(v___x_557_, v___x_556_);
    return v___x_558_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_559_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
    v___x_561_ = l_Lean_Name_str___override(v___x_560_, v___x_559_);
    return v___x_561_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = leanh::lean_unsigned_to_nat(2);
    v___x_563_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
    v___x_564_ = l_Lean_Name_num___override(v___x_563_, v___x_562_);
    return v___x_564_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
    v___x_567_ = 0;
    v___x_568_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
    v___x_569_ = l_Lean_registerTraceClass(v___x_566_, v___x_567_, v___x_568_);
    return v___x_569_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2____boxed(
    mut v_a_570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_571_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
    return v_res_571_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = leanh::lean_unsigned_to_nat(3362372890);
    v___x_579_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_580_ = l_Lean_Name_num___override(v___x_579_, v___x_578_);
    return v___x_580_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_582_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
    v___x_583_ = l_Lean_Name_str___override(v___x_582_, v___x_581_);
    return v___x_583_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
    v___x_586_ = l_Lean_Name_str___override(v___x_585_, v___x_584_);
    return v___x_586_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_587_ = leanh::lean_unsigned_to_nat(2);
    v___x_588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
    v___x_589_ = l_Lean_Name_num___override(v___x_588_, v___x_587_);
    return v___x_589_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: u8 = 0;
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_591_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
    v___x_592_ = 0;
    v___x_593_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
    v___x_594_ = l_Lean_registerTraceClass(v___x_591_, v___x_592_, v___x_593_);
    return v___x_594_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2____boxed(
    mut v_a_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
    return v_res_596_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_616_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_;
    v___x_617_ = 0;
    v___x_618_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_;
    v___x_619_ = l_Lean_registerTraceClass(v___x_616_, v___x_617_, v___x_618_);
    return v___x_619_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2____boxed(
    mut v_a_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
    return v_res_621_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = leanh::lean_unsigned_to_nat(3823406372);
    v___x_629_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_630_ = l_Lean_Name_num___override(v___x_629_, v___x_628_);
    return v___x_630_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
    v___x_633_ = l_Lean_Name_str___override(v___x_632_, v___x_631_);
    return v___x_633_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
    v___x_635_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
    v___x_636_ = l_Lean_Name_str___override(v___x_635_, v___x_634_);
    return v___x_636_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_637_ = leanh::lean_unsigned_to_nat(2);
    v___x_638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
    v___x_639_ = l_Lean_Name_num___override(v___x_638_, v___x_637_);
    return v___x_639_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_641_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
    v___x_642_ = 0;
    v___x_643_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
    v___x_644_ = l_Lean_registerTraceClass(v___x_641_, v___x_642_, v___x_643_);
    return v___x_644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2____boxed(
    mut v_a_645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
    return v_res_646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: u8 = 0;
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_;
    v___x_667_ = 0;
    v___x_668_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_;
    v___x_669_ = l_Lean_registerTraceClass(v___x_666_, v___x_667_, v___x_668_);
    return v___x_669_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2____boxed(
    mut v_a_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
    return v_res_671_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(
    mut v___x_672_: u8,
    mut v___y_673_: *mut leanh::LeanObject,
    mut v___y_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
    mut v___y_676_: *mut leanh::LeanObject,
    mut v___y_677_: *mut leanh::LeanObject,
    mut v___y_678_: *mut leanh::LeanObject,
    mut v___y_679_: *mut leanh::LeanObject,
    mut v___y_680_: *mut leanh::LeanObject,
    mut v___y_681_: *mut leanh::LeanObject,
    mut v___y_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = leanh::lean_box((v___x_672_) as usize);
    v___x_685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_685_, 0, v___x_684_);
    return v___x_685_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(
    mut v___x_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
    mut v___y_689_: *mut leanh::LeanObject,
    mut v___y_690_: *mut leanh::LeanObject,
    mut v___y_691_: *mut leanh::LeanObject,
    mut v___y_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
    mut v___y_695_: *mut leanh::LeanObject,
    mut v___y_696_: *mut leanh::LeanObject,
    mut v___y_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_495__boxed_698_: u8 = 0;
    let mut v_res_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_495__boxed_698_ = (leanh::lean_unbox(v___x_686_) as u8);
    v_res_699_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(v___x_495__boxed_698_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
    leanh::lean_dec(v___y_696_);
    leanh::lean_dec_ref(v___y_695_);
    leanh::lean_dec(v___y_694_);
    leanh::lean_dec_ref(v___y_693_);
    leanh::lean_dec(v___y_692_);
    leanh::lean_dec_ref(v___y_691_);
    leanh::lean_dec(v___y_690_);
    leanh::lean_dec_ref(v___y_689_);
    leanh::lean_dec(v___y_688_);
    leanh::lean_dec(v___y_687_);
    return v_res_699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_711_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___x_712_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___x_713_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___f_714_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___x_715_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___x_716_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___x_717_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
    v___x_718_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(
        v___x_710_, v___x_711_, v___x_712_, v___x_713_, v___f_714_, v___x_715_, v___x_716_,
        v___x_717_,
    );
    return v___x_718_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(
    mut v_a_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
    return v_res_720_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Eq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Eq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC(builtin);
}