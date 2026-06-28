// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.Search Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM Lean.Meta.Tactic.Grind.Arith.Cutsat.Model Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename Lean.Meta.Tactic.Grind.Arith.Cutsat.Action
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Action::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action, l_Lean_Meta_Grind_Action_lia___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::CommRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::DvdCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::EqCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr,
    l_Lean_Meta_Grind_Arith_Cutsat_internalize___boxed,
    l_Lean_Meta_Grind_Arith_Cutsat_processNewDiseq___boxed,
    l_Lean_Meta_Grind_Arith_Cutsat_processNewEq___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Inv::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv,
    l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::LeCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::MBTC::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC,
    l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Nat::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Search::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search,
    l_Lean_Meta_Grind_Arith_Cutsat_check___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::SearchM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_SolverExtension_setMethods___redArg;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,622053547050603573 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,7655114909728474417 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [67, 117, 116, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,780552250419057991 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,3634664711417579578 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,6930698414953089627 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12306401774593766835 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,5665047452812330277 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,8954872553652790145 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,5248097571322690679 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,5432797068193640134 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,9777929220259628407 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,10024563492529869834 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,18122738536244428974 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,3327982928462436947 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,275722381374651909 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,5219376284276193761 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,9956735648171087831 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 1544613409 as usize) << 1) | 1) as *mut LeanObject,702493359134491732 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,6418353160703673371 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,17049393046083141115 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,10470443008075096974 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 110, 108, 105, 110, 101, 97, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value) as *mut LeanObject,10513396622713174637 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 111, 100, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject,10981442452371052972 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 1905195225 as usize) << 1) | 1) as *mut LeanObject,7335155797465000313 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11847493791262316010 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,17013275544136482966 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17722434022519979991 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,10199653630302390726 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 537780665 as usize) << 1) | 1) as *mut LeanObject,9575316781377447800 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,588857437099370879 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,13370201228433130503 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17182912612897113714 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,10199653630302390726 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value) as *mut LeanObject,16175042957003990705 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,10199653630302390726 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value) as *mut LeanObject,5443962459141360856 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,10199653630302390726 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value) as *mut LeanObject,10228816052197840364 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11074150007773075224 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value) as *mut LeanObject,10199653630302390726 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value) as *mut LeanObject,4162367480076971315 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 1839615665 as usize) << 1) | 1) as *mut LeanObject,3263680116930860470 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,1002445705070064529 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,9652780573170751913 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,8944769040690765268 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 117, 98, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,1504612912130463053 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 179901175 as usize) << 1) | 1) as *mut LeanObject,9334766612628687834 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,17980702923455892085 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11645718664358888245 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,2498636243599082744 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 101, 97, 114, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 798741302 as usize) << 1) | 1) as *mut LeanObject,16504791611975050691 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,7203529609579111640 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,4047357852318910076 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17846360386279065125 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject,4908033850348550690 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 2124775375 as usize) << 1) | 1) as *mut LeanObject,2410180428712785015 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,1658546274742731964 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11274285310098184200 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17472406537924958857 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 105, 103, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject,7768729064680374671 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 1019473888 as usize) << 1) | 1) as *mut LeanObject,9184000729657689968 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,4365893915432687143 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,5642635481494999279 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,13377922322440991466 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 102, 108, 105, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject,4445940582693740952 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 655095259 as usize) << 1) | 1) as *mut LeanObject,4006572524847718491 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,5654238180441688160 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,4598254671303651140 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,1264987816743471389 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 97, 99, 107, 116, 114, 97, 99, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value) as *mut LeanObject,4152774248855280706 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value) as *mut LeanObject,1477802454752751138 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value) as *mut LeanObject,5642750555733400539 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 110, 115, 116, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value) as *mut LeanObject,4314520313759331442 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 111, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value) as *mut LeanObject,8688716430328349044 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject,3226274256350322668 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 372033 as usize) << 1) | 1) as *mut LeanObject,10996178212458175548 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,11171850926045398931 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,14667362924722098387 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,373029014378656214 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 108, 105, 109, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,12441483040187581015 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject,14181106342218592 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,((( 69582620 as usize) << 1) | 1) as *mut LeanObject,8873957852738897299 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,968567714633647688 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value) as *mut LeanObject,13213307085098032972 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,16350760858341059701 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Cutsat_internalize___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Cutsat_processNewEq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Cutsat_processNewDiseq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_lia___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Cutsat_check___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    v___x_663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_664_ = 0;
    v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_666_ = l_Lean_registerTraceClass(v___x_663_, v___x_664_, v___x_665_);
    return v___x_666_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2____boxed(
    mut v_a_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_668_: *mut LeanObject = core::ptr::null_mut();
    v_res_668_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
    return v_res_668_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    v___x_674_ = lean_unsigned_to_nat(2341206022);
    v___x_675_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_676_ = l_Lean_Name_num___override(v___x_675_, v___x_674_);
    return v___x_676_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    v___x_677_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_678_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
    v___x_679_ = l_Lean_Name_str___override(v___x_678_, v___x_677_);
    return v___x_679_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_681_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
    v___x_682_ = l_Lean_Name_str___override(v___x_681_, v___x_680_);
    return v___x_682_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    v___x_683_ = lean_unsigned_to_nat(2);
    v___x_684_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
    v___x_685_ = l_Lean_Name_num___override(v___x_684_, v___x_683_);
    return v___x_685_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_;
    v___x_688_ = 0;
    v___x_689_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
    v___x_690_ = l_Lean_registerTraceClass(v___x_687_, v___x_688_, v___x_689_);
    return v___x_690_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2____boxed(
    mut v_a_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_692_: *mut LeanObject = core::ptr::null_mut();
    v_res_692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
    return v_res_692_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u8 = 0;
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_;
    v___x_712_ = 0;
    v___x_713_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_;
    v___x_714_ = l_Lean_registerTraceClass(v___x_711_, v___x_712_, v___x_713_);
    return v___x_714_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2____boxed(
    mut v_a_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
    return v_res_716_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_;
    v___x_736_ = 0;
    v___x_737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_;
    v___x_738_ = l_Lean_registerTraceClass(v___x_735_, v___x_736_, v___x_737_);
    return v___x_738_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2____boxed(
    mut v_a_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_740_: *mut LeanObject = core::ptr::null_mut();
    v_res_740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
    return v_res_740_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = lean_unsigned_to_nat(3140426734);
    v___x_748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_749_ = l_Lean_Name_num___override(v___x_748_, v___x_747_);
    return v___x_749_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_751_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
    v___x_752_ = l_Lean_Name_str___override(v___x_751_, v___x_750_);
    return v___x_752_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    v___x_753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_754_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
    v___x_755_ = l_Lean_Name_str___override(v___x_754_, v___x_753_);
    return v___x_755_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ = lean_unsigned_to_nat(2);
    v___x_757_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
    v___x_758_ = l_Lean_Name_num___override(v___x_757_, v___x_756_);
    return v___x_758_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___x_760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_;
    v___x_761_ = 0;
    v___x_762_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
    v___x_763_ = l_Lean_registerTraceClass(v___x_760_, v___x_761_, v___x_762_);
    return v___x_763_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2____boxed(
    mut v_a_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_765_: *mut LeanObject = core::ptr::null_mut();
    v_res_765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
    return v_res_765_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = lean_unsigned_to_nat(2860508919);
    v___x_773_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_774_ = l_Lean_Name_num___override(v___x_773_, v___x_772_);
    return v___x_774_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_776_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
    v___x_777_ = l_Lean_Name_str___override(v___x_776_, v___x_775_);
    return v___x_777_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v___x_778_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_779_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
    v___x_780_ = l_Lean_Name_str___override(v___x_779_, v___x_778_);
    return v___x_780_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    v___x_781_ = lean_unsigned_to_nat(2);
    v___x_782_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
    v___x_783_ = l_Lean_Name_num___override(v___x_782_, v___x_781_);
    return v___x_783_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_;
    v___x_786_ = 0;
    v___x_787_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
    v___x_788_ = l_Lean_registerTraceClass(v___x_785_, v___x_786_, v___x_787_);
    return v___x_788_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2____boxed(
    mut v_a_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
    return v_res_790_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_797_ = lean_unsigned_to_nat(2288204289);
    v___x_798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_799_ = l_Lean_Name_num___override(v___x_798_, v___x_797_);
    return v___x_799_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v___x_800_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_801_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
    v___x_802_ = l_Lean_Name_str___override(v___x_801_, v___x_800_);
    return v___x_802_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_804_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
    v___x_805_ = l_Lean_Name_str___override(v___x_804_, v___x_803_);
    return v___x_805_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_806_ = lean_unsigned_to_nat(2);
    v___x_807_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
    v___x_808_ = l_Lean_Name_num___override(v___x_807_, v___x_806_);
    return v___x_808_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    v___x_810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_;
    v___x_811_ = 0;
    v___x_812_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
    v___x_813_ = l_Lean_registerTraceClass(v___x_810_, v___x_811_, v___x_812_);
    return v___x_813_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2____boxed(
    mut v_a_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_815_: *mut LeanObject = core::ptr::null_mut();
    v_res_815_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
    return v_res_815_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_;
    v___x_835_ = 0;
    v___x_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_;
    v___x_837_ = l_Lean_registerTraceClass(v___x_834_, v___x_835_, v___x_836_);
    return v___x_837_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2____boxed(
    mut v_a_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_839_: *mut LeanObject = core::ptr::null_mut();
    v_res_839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
    return v_res_839_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_;
    v___x_861_ = 0;
    v___x_862_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_;
    v___x_863_ = l_Lean_registerTraceClass(v___x_860_, v___x_861_, v___x_862_);
    return v___x_863_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2____boxed(
    mut v_a_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_865_: *mut LeanObject = core::ptr::null_mut();
    v_res_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
    return v_res_865_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_;
    v___x_886_ = 0;
    v___x_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_;
    v___x_888_ = l_Lean_registerTraceClass(v___x_885_, v___x_886_, v___x_887_);
    return v___x_888_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2____boxed(
    mut v_a_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_890_: *mut LeanObject = core::ptr::null_mut();
    v_res_890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
    return v_res_890_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_911_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_;
    v___x_912_ = 1;
    v___x_913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_;
    v___x_914_ = l_Lean_registerTraceClass(v___x_911_, v___x_912_, v___x_913_);
    return v___x_914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2____boxed(
    mut v_a_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
    v_res_916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
    return v_res_916_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    v___x_937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_;
    v___x_938_ = 1;
    v___x_939_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_;
    v___x_940_ = l_Lean_registerTraceClass(v___x_937_, v___x_938_, v___x_939_);
    return v___x_940_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2____boxed(
    mut v_a_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_942_: *mut LeanObject = core::ptr::null_mut();
    v_res_942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
    return v_res_942_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    v___x_963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_;
    v___x_964_ = 1;
    v___x_965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_;
    v___x_966_ = l_Lean_registerTraceClass(v___x_963_, v___x_964_, v___x_965_);
    return v___x_966_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2____boxed(
    mut v_a_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v_res_968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
    return v_res_968_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = lean_unsigned_to_nat(2719854357);
    v___x_977_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_978_ = l_Lean_Name_num___override(v___x_977_, v___x_976_);
    return v___x_978_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_980_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
    v___x_981_ = l_Lean_Name_str___override(v___x_980_, v___x_979_);
    return v___x_981_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_983_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
    v___x_984_ = l_Lean_Name_str___override(v___x_983_, v___x_982_);
    return v___x_984_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ = lean_unsigned_to_nat(2);
    v___x_986_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
    v___x_987_ = l_Lean_Name_num___override(v___x_986_, v___x_985_);
    return v___x_987_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_989_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_;
    v___x_990_ = 1;
    v___x_991_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
    v___x_992_ = l_Lean_registerTraceClass(v___x_989_, v___x_990_, v___x_991_);
    return v___x_992_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2____boxed(
    mut v_a_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
    return v_res_994_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    v___x_1001_ = lean_unsigned_to_nat(2389350560);
    v___x_1002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1003_ = l_Lean_Name_num___override(v___x_1002_, v___x_1001_);
    return v___x_1003_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1005_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
    v___x_1006_ = l_Lean_Name_str___override(v___x_1005_, v___x_1004_);
    return v___x_1006_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1008_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
    v___x_1009_ = l_Lean_Name_str___override(v___x_1008_, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = lean_unsigned_to_nat(2);
    v___x_1011_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
    v___x_1012_ = l_Lean_Name_num___override(v___x_1011_, v___x_1010_);
    return v___x_1012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: u8 = 0;
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    v___x_1014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_;
    v___x_1015_ = 0;
    v___x_1016_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
    v___x_1017_ = l_Lean_registerTraceClass(v___x_1014_, v___x_1015_, v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2____boxed(
    mut v_a_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
    return v_res_1019_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    v___x_1026_ = lean_unsigned_to_nat(2594082301);
    v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1028_ = l_Lean_Name_num___override(v___x_1027_, v___x_1026_);
    return v___x_1028_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    v___x_1029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1030_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
    v___x_1031_ = l_Lean_Name_str___override(v___x_1030_, v___x_1029_);
    return v___x_1031_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1033_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
    v___x_1034_ = l_Lean_Name_str___override(v___x_1033_, v___x_1032_);
    return v___x_1034_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1035_ = lean_unsigned_to_nat(2);
    v___x_1036_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
    v___x_1037_ = l_Lean_Name_num___override(v___x_1036_, v___x_1035_);
    return v___x_1037_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    v___x_1039_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_;
    v___x_1040_ = 0;
    v___x_1041_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
    v___x_1042_ = l_Lean_registerTraceClass(v___x_1039_, v___x_1040_, v___x_1041_);
    return v___x_1042_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2____boxed(
    mut v_a_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1044_: *mut LeanObject = core::ptr::null_mut();
    v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
    return v_res_1044_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ = lean_unsigned_to_nat(3902918421);
    v___x_1053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1054_ = l_Lean_Name_num___override(v___x_1053_, v___x_1052_);
    return v___x_1054_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1055_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1056_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
    v___x_1057_ = l_Lean_Name_str___override(v___x_1056_, v___x_1055_);
    return v___x_1057_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    v___x_1058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_;
    v___x_1059_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
    v___x_1060_ = l_Lean_Name_str___override(v___x_1059_, v___x_1058_);
    return v___x_1060_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    v___x_1061_ = lean_unsigned_to_nat(2);
    v___x_1062_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
    v___x_1063_ = l_Lean_Name_num___override(v___x_1062_, v___x_1061_);
    return v___x_1063_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    v___x_1065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_;
    v___x_1066_ = 0;
    v___x_1067_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
    v___x_1068_ = l_Lean_registerTraceClass(v___x_1065_, v___x_1066_, v___x_1067_);
    return v___x_1068_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2____boxed(
    mut v_a_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1070_: *mut LeanObject = core::ptr::null_mut();
    v_res_1070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
    return v_res_1070_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: u8 = 0;
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    v___x_1091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_;
    v___x_1092_ = 0;
    v___x_1093_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_;
    v___x_1094_ = l_Lean_registerTraceClass(v___x_1091_, v___x_1092_, v___x_1093_);
    return v___x_1094_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2____boxed(
    mut v_a_1095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1096_: *mut LeanObject = core::ptr::null_mut();
    v_res_1096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
    return v_res_1096_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: u8 = 0;
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    v___x_1116_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_;
    v___x_1117_ = 0;
    v___x_1118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_;
    v___x_1119_ = l_Lean_registerTraceClass(v___x_1116_, v___x_1117_, v___x_1118_);
    return v___x_1119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2____boxed(
    mut v_a_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1121_: *mut LeanObject = core::ptr::null_mut();
    v_res_1121_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
    return v_res_1121_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    v___x_1130_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_1131_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1132_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1133_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1134_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1137_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_;
    v___x_1138_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(
        v___x_1130_,
        v___x_1131_,
        v___x_1132_,
        v___x_1133_,
        v___x_1134_,
        v___x_1135_,
        v___x_1136_,
        v___x_1137_,
    );
    return v___x_1138_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2____boxed(
    mut v_a_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1140_: *mut LeanObject = core::ptr::null_mut();
    v_res_1140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
    return v_res_1140_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
}
