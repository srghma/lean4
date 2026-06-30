// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Lookahead
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.EMatchAction
use crate::ffi::{
    lean_grind_process_new_facts, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::l_Lean_mkArrow;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNot,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_getFalseExpr___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    l_Lean_Meta_Grind_Action_andThen, l_Lean_Meta_Grind_Action_loop___redArg,
    l_Lean_Meta_Grind_Action_orElse, l_Lean_Meta_Grind_Action_run,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchAction::{
    initialize_Lean_Meta_Tactic_Grind_EMatchAction, l_Lean_Meta_Grind_Action_instantiate___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Intro::{
    l_Lean_Meta_Grind_Action_assertAll___boxed, l_Lean_Meta_Grind_Action_intros___boxed,
    l_Lean_Meta_Grind_Solvers_mkAction,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Split::{
    initialize_Lean_Meta_Tactic_Grind_Split, l_Lean_Meta_Grind_Action_splitNext___boxed,
    l_Lean_Meta_Grind_checkSplitStatus, runtime_initialize_Lean_Meta_Tactic_Grind_Split,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_SplitInfo_getExpr,
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_isInconsistent___redArg, l_Lean_Meta_Grind_pushEqTrue___redArg,
    l_Lean_Meta_Grind_updateLastTag, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0_value: leanh::LeanClosureObject<2> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_splitNext___boxed as *const core::ffi::c_void, m_arity: 15, m_num_fixed: 2, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_assertAll___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_instantiate___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed as *const core::ffi::c_void, m_arity: 14, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [111, 102, 95, 108, 111, 111, 107, 97, 104, 101, 97, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__2_value) as *mut leanh::LeanObject,7634456179798618838 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 111, 111, 107, 97, 104, 101, 97, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value) as *mut leanh::LeanObject,13680939433876848140 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__7_value) as *mut leanh::LeanObject,4137541495311671234 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__9_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__5_value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__6_value) as *mut leanh::LeanObject,13680939433876848140 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__12_value) as *mut leanh::LeanObject,8315095477535384964 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations()
-> *mut leanh::LeanObject {
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = leanh::lean_unsigned_to_nat(10000);
    return v___x_1295_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(
    mut v___f_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___closed__0;
    v___x_1315_ = l_Lean_Meta_Grind_Action_orElse(
        v___x_1314_,
        v___f_1300_,
        v___y_1301_,
        v___y_1302_,
        v___y_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
        v___y_1309_,
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
    );
    return v___x_1315_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0___boxed(
    mut v___f_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__0(
        v___f_1316_,
        v___y_1317_,
        v___y_1318_,
        v___y_1319_,
        v___y_1320_,
        v___y_1321_,
        v___y_1322_,
        v___y_1323_,
        v___y_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
    );
    leanh::lean_dec(v___y_1328_);
    leanh::lean_dec_ref(v___y_1327_);
    leanh::lean_dec(v___y_1326_);
    leanh::lean_dec_ref(v___y_1325_);
    leanh::lean_dec(v___y_1324_);
    leanh::lean_dec_ref(v___y_1323_);
    leanh::lean_dec(v___y_1322_);
    leanh::lean_dec_ref(v___y_1321_);
    leanh::lean_dec(v___y_1320_);
    return v_res_1330_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(
    mut v_a_1331_: *mut leanh::LeanObject,
    mut v___f_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
    mut v___y_1337_: *mut leanh::LeanObject,
    mut v___y_1338_: *mut leanh::LeanObject,
    mut v___y_1339_: *mut leanh::LeanObject,
    mut v___y_1340_: *mut leanh::LeanObject,
    mut v___y_1341_: *mut leanh::LeanObject,
    mut v___y_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
    mut v___y_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_Meta_Grind_Action_orElse(
        v_a_1331_,
        v___f_1332_,
        v___y_1333_,
        v___y_1334_,
        v___y_1335_,
        v___y_1336_,
        v___y_1337_,
        v___y_1338_,
        v___y_1339_,
        v___y_1340_,
        v___y_1341_,
        v___y_1342_,
        v___y_1343_,
        v___y_1344_,
    );
    return v___x_1346_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed(
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v___f_1348_: *mut leanh::LeanObject,
    mut v___y_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
    mut v___y_1358_: *mut leanh::LeanObject,
    mut v___y_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1(
        v_a_1347_,
        v___f_1348_,
        v___y_1349_,
        v___y_1350_,
        v___y_1351_,
        v___y_1352_,
        v___y_1353_,
        v___y_1354_,
        v___y_1355_,
        v___y_1356_,
        v___y_1357_,
        v___y_1358_,
        v___y_1359_,
        v___y_1360_,
    );
    leanh::lean_dec(v___y_1360_);
    leanh::lean_dec_ref(v___y_1359_);
    leanh::lean_dec(v___y_1358_);
    leanh::lean_dec_ref(v___y_1357_);
    leanh::lean_dec(v___y_1356_);
    leanh::lean_dec_ref(v___y_1355_);
    leanh::lean_dec(v___y_1354_);
    leanh::lean_dec_ref(v___y_1353_);
    leanh::lean_dec(v___y_1352_);
    return v_res_1362_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(
    mut v___f_1363_: *mut leanh::LeanObject,
    mut v___y_1364_: *mut leanh::LeanObject,
    mut v___y_1365_: *mut leanh::LeanObject,
    mut v___y_1366_: *mut leanh::LeanObject,
    mut v___y_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
    mut v___y_1369_: *mut leanh::LeanObject,
    mut v___y_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
    mut v___y_1372_: *mut leanh::LeanObject,
    mut v___y_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
    mut v___y_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = leanh::lean_unsigned_to_nat(10000);
    v___x_1378_ = l_Lean_Meta_Grind_Action_loop___redArg(
        v___x_1377_,
        v___f_1363_,
        v___y_1364_,
        v___y_1366_,
        v___y_1367_,
        v___y_1368_,
        v___y_1369_,
        v___y_1370_,
        v___y_1371_,
        v___y_1372_,
        v___y_1373_,
        v___y_1374_,
        v___y_1375_,
    );
    return v___x_1378_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed(
    mut v___f_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
    mut v___y_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2(
        v___f_1379_,
        v___y_1380_,
        v___y_1381_,
        v___y_1382_,
        v___y_1383_,
        v___y_1384_,
        v___y_1385_,
        v___y_1386_,
        v___y_1387_,
        v___y_1388_,
        v___y_1389_,
        v___y_1390_,
        v___y_1391_,
    );
    leanh::lean_dec(v___y_1391_);
    leanh::lean_dec_ref(v___y_1390_);
    leanh::lean_dec(v___y_1389_);
    leanh::lean_dec_ref(v___y_1388_);
    leanh::lean_dec(v___y_1387_);
    leanh::lean_dec_ref(v___y_1386_);
    leanh::lean_dec(v___y_1385_);
    leanh::lean_dec_ref(v___y_1384_);
    leanh::lean_dec(v___y_1383_);
    leanh::lean_dec_ref(v___y_1381_);
    return v_res_1393_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(
    mut v___f_1395_: *mut leanh::LeanObject,
    mut v___y_1396_: *mut leanh::LeanObject,
    mut v___y_1397_: *mut leanh::LeanObject,
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
    mut v___y_1402_: *mut leanh::LeanObject,
    mut v___y_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___closed__0;
    v___x_1410_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_1409_,
        v___f_1395_,
        v___y_1396_,
        v___y_1397_,
        v___y_1398_,
        v___y_1399_,
        v___y_1400_,
        v___y_1401_,
        v___y_1402_,
        v___y_1403_,
        v___y_1404_,
        v___y_1405_,
        v___y_1406_,
        v___y_1407_,
    );
    return v___x_1410_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed(
    mut v___f_1411_: *mut leanh::LeanObject,
    mut v___y_1412_: *mut leanh::LeanObject,
    mut v___y_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
    mut v___y_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3(
        v___f_1411_,
        v___y_1412_,
        v___y_1413_,
        v___y_1414_,
        v___y_1415_,
        v___y_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
        v___y_1420_,
        v___y_1421_,
        v___y_1422_,
        v___y_1423_,
    );
    leanh::lean_dec(v___y_1423_);
    leanh::lean_dec_ref(v___y_1422_);
    leanh::lean_dec(v___y_1421_);
    leanh::lean_dec_ref(v___y_1420_);
    leanh::lean_dec(v___y_1419_);
    leanh::lean_dec_ref(v___y_1418_);
    leanh::lean_dec(v___y_1417_);
    leanh::lean_dec_ref(v___y_1416_);
    leanh::lean_dec(v___y_1415_);
    return v_res_1425_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(
    mut v___x_1426_: *mut leanh::LeanObject,
    mut v___f_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
    mut v___y_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
    mut v___y_1436_: *mut leanh::LeanObject,
    mut v___y_1437_: *mut leanh::LeanObject,
    mut v___y_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_1426_,
        v___f_1427_,
        v___y_1428_,
        v___y_1429_,
        v___y_1430_,
        v___y_1431_,
        v___y_1432_,
        v___y_1433_,
        v___y_1434_,
        v___y_1435_,
        v___y_1436_,
        v___y_1437_,
        v___y_1438_,
        v___y_1439_,
    );
    return v___x_1441_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed(
    mut v___x_1442_: *mut leanh::LeanObject,
    mut v___f_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
    mut v___y_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
    mut v___y_1455_: *mut leanh::LeanObject,
    mut v___y_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1457_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4(
        v___x_1442_,
        v___f_1443_,
        v___y_1444_,
        v___y_1445_,
        v___y_1446_,
        v___y_1447_,
        v___y_1448_,
        v___y_1449_,
        v___y_1450_,
        v___y_1451_,
        v___y_1452_,
        v___y_1453_,
        v___y_1454_,
        v___y_1455_,
    );
    leanh::lean_dec(v___y_1455_);
    leanh::lean_dec_ref(v___y_1454_);
    leanh::lean_dec(v___y_1453_);
    leanh::lean_dec_ref(v___y_1452_);
    leanh::lean_dec(v___y_1451_);
    leanh::lean_dec_ref(v___y_1450_);
    leanh::lean_dec(v___y_1449_);
    leanh::lean_dec_ref(v___y_1448_);
    leanh::lean_dec(v___y_1447_);
    return v_res_1457_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(
    mut v_goal_1461_: *mut leanh::LeanObject,
    mut v_generation_1462_: *mut leanh::LeanObject,
    mut v_a_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_a_1470_: *mut leanh::LeanObject,
    mut v_a_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gs_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v_head_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_a_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_a_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v_ref_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1473_ = l_Lean_Meta_Grind_Solvers_mkAction();
                if leanh::lean_obj_tag(v___x_1473_) == 0 {
                    v_a_1474_ = leanh::lean_ctor_get(v___x_1473_, 0);
                    leanh::lean_inc(v_a_1474_);
                    leanh::lean_dec_ref_known(v___x_1473_, 1);
                    v___f_1475_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___closed__1;
                    v___f_1476_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__1___boxed as *mut core::ffi::c_void, 15, 2);
                    leanh::lean_closure_set(v___f_1476_, 0, v_a_1474_);
                    leanh::lean_closure_set(v___f_1476_, 1, v___f_1475_);
                    v___f_1477_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__2___boxed as *mut core::ffi::c_void, 14, 1);
                    leanh::lean_closure_set(v___f_1477_, 0, v___f_1476_);
                    v___f_1478_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__3___boxed as *mut core::ffi::c_void, 14, 1);
                    leanh::lean_closure_set(v___f_1478_, 0, v___f_1477_);
                    v___x_1479_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_intros___boxed as *mut core::ffi::c_void,
                        14,
                        1,
                    );
                    leanh::lean_closure_set(v___x_1479_, 0, v_generation_1462_);
                    v___f_1480_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___lam__4___boxed as *mut core::ffi::c_void, 15, 2);
                    leanh::lean_closure_set(v___f_1480_, 0, v___x_1479_);
                    leanh::lean_closure_set(v___f_1480_, 1, v___f_1478_);
                    leanh::lean_inc_ref(v_goal_1461_);
                    v___x_1481_ = l_Lean_Meta_Grind_Action_run(
                        v_goal_1461_,
                        v___f_1480_,
                        v_a_1463_,
                        v_a_1464_,
                        v_a_1465_,
                        v_a_1466_,
                        v_a_1467_,
                        v_a_1468_,
                        v_a_1469_,
                        v_a_1470_,
                        v_a_1471_,
                    );
                    if leanh::lean_obj_tag(v___x_1481_) == 0 {
                        v_a_1482_ = leanh::lean_ctor_get(v___x_1481_, 0);
                        v_isSharedCheck_1508_ =
                            (!leanh::lean_is_exclusive(v___x_1481_)) as u8;
                        if v_isSharedCheck_1508_ == 0 {
                            v___x_1484_ = v___x_1481_;
                            v_isShared_1485_ = v_isSharedCheck_1508_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1482_);
                            leanh::lean_dec(v___x_1481_);
                            v___x_1484_ = leanh::lean_box(0);
                            v_isShared_1485_ = v_isSharedCheck_1508_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_goal_1461_);
                        v_a_1509_ = leanh::lean_ctor_get(v___x_1481_, 0);
                        v_isSharedCheck_1516_ =
                            (!leanh::lean_is_exclusive(v___x_1481_)) as u8;
                        if v_isSharedCheck_1516_ == 0 {
                            v___x_1511_ = v___x_1481_;
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1509_);
                            leanh::lean_dec(v___x_1481_);
                            v___x_1511_ = leanh::lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_generation_1462_);
                    leanh::lean_dec_ref(v_goal_1461_);
                    v_a_1517_ = leanh::lean_ctor_get(v___x_1473_, 0);
                    v_isSharedCheck_1529_ = (!leanh::lean_is_exclusive(v___x_1473_)) as u8;
                    if v_isSharedCheck_1529_ == 0 {
                        v___x_1519_ = v___x_1473_;
                        v_isShared_1520_ = v_isSharedCheck_1529_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1517_);
                        leanh::lean_dec(v___x_1473_);
                        v___x_1519_ = leanh::lean_box(0);
                        v_isShared_1520_ = v_isSharedCheck_1529_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1482_) == 0 {
                    leanh::lean_dec_ref_known(v_a_1482_, 1);
                    leanh::lean_dec_ref(v_goal_1461_);
                    v___x_1486_ = leanh::lean_box(0);
                    if v_isShared_1485_ == 0 {
                        leanh::lean_ctor_set(v___x_1484_, 0, v___x_1486_);
                        v___x_1488_ = v___x_1484_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
                        v___x_1488_ = v_reuseFailAlloc_1489_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_gs_1490_ = leanh::lean_ctor_get(v_a_1482_, 0);
                    v_isSharedCheck_1507_ = (!leanh::lean_is_exclusive(v_a_1482_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1492_ = v_a_1482_;
                        v_isShared_1493_ = v_isSharedCheck_1507_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gs_1490_);
                        leanh::lean_dec(v_a_1482_);
                        v___x_1492_ = leanh::lean_box(0);
                        v_isShared_1493_ = v_isSharedCheck_1507_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1488_;
            }
            3 => {
                if leanh::lean_obj_tag(v_gs_1490_) == 1 {
                    leanh::lean_dec_ref(v_goal_1461_);
                    v_head_1494_ = leanh::lean_ctor_get(v_gs_1490_, 0);
                    leanh::lean_inc(v_head_1494_);
                    leanh::lean_dec_ref_known(v_gs_1490_, 2);
                    if v_isShared_1493_ == 0 {
                        leanh::lean_ctor_set(v___x_1492_, 0, v_head_1494_);
                        v___x_1496_ = v___x_1492_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_head_1494_);
                        v___x_1496_ = v_reuseFailAlloc_1500_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_gs_1490_);
                    if v_isShared_1493_ == 0 {
                        leanh::lean_ctor_set(v___x_1492_, 0, v_goal_1461_);
                        v___x_1502_ = v___x_1492_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_goal_1461_);
                        v___x_1502_ = v_reuseFailAlloc_1506_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1485_ == 0 {
                    leanh::lean_ctor_set(v___x_1484_, 0, v___x_1496_);
                    v___x_1498_ = v___x_1484_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1498_;
            }
            6 => {
                if v_isShared_1485_ == 0 {
                    leanh::lean_ctor_set(v___x_1484_, 0, v___x_1502_);
                    v___x_1504_ = v___x_1484_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1504_;
            }
            8 => {
                if v_isShared_1512_ == 0 {
                    v___x_1514_ = v___x_1511_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
                    v___x_1514_ = v_reuseFailAlloc_1515_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1514_;
            }
            10 => {
                v_ref_1521_ = leanh::lean_ctor_get(v_a_1470_, 5);
                v___x_1522_ = lean_io_error_to_string(v_a_1517_);
                v___x_1523_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1523_, 0, v___x_1522_);
                v___x_1524_ = l_Lean_MessageData_ofFormat(v___x_1523_);
                leanh::lean_inc(v_ref_1521_);
                v___x_1525_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1525_, 0, v_ref_1521_);
                leanh::lean_ctor_set(v___x_1525_, 1, v___x_1524_);
                if v_isShared_1520_ == 0 {
                    leanh::lean_ctor_set(v___x_1519_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1519_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
                    v___x_1527_ = v_reuseFailAlloc_1528_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve___boxed(
    mut v_goal_1530_: *mut leanh::LeanObject,
    mut v_generation_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_a_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
    mut v_a_1535_: *mut leanh::LeanObject,
    mut v_a_1536_: *mut leanh::LeanObject,
    mut v_a_1537_: *mut leanh::LeanObject,
    mut v_a_1538_: *mut leanh::LeanObject,
    mut v_a_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_a_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(
        v_goal_1530_,
        v_generation_1531_,
        v_a_1532_,
        v_a_1533_,
        v_a_1534_,
        v_a_1535_,
        v_a_1536_,
        v_a_1537_,
        v_a_1538_,
        v_a_1539_,
        v_a_1540_,
    );
    leanh::lean_dec(v_a_1540_);
    leanh::lean_dec_ref(v_a_1539_);
    leanh::lean_dec(v_a_1538_);
    leanh::lean_dec_ref(v_a_1537_);
    leanh::lean_dec(v_a_1536_);
    leanh::lean_dec_ref(v_a_1535_);
    leanh::lean_dec(v_a_1534_);
    leanh::lean_dec_ref(v_a_1533_);
    leanh::lean_dec(v_a_1532_);
    return v_res_1542_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(
    mut v_e_1543_: *mut leanh::LeanObject,
    mut v___y_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut v_unused_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1546_ = l_Lean_Expr_hasMVar(v_e_1543_);
                if v___x_1546_ == 0 {
                    v___x_1547_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1547_, 0, v_e_1543_);
                    return v___x_1547_;
                } else {
                    v___x_1548_ = lean_st_ref_get(v___y_1544_);
                    v_mctx_1549_ = leanh::lean_ctor_get(v___x_1548_, 0);
                    leanh::lean_inc_ref(v_mctx_1549_);
                    leanh::lean_dec(v___x_1548_);
                    v___x_1550_ = l_Lean_instantiateMVarsCore(v_mctx_1549_, v_e_1543_);
                    v_fst_1551_ = leanh::lean_ctor_get(v___x_1550_, 0);
                    leanh::lean_inc(v_fst_1551_);
                    v_snd_1552_ = leanh::lean_ctor_get(v___x_1550_, 1);
                    leanh::lean_inc(v_snd_1552_);
                    leanh::lean_dec_ref(v___x_1550_);
                    v___x_1553_ = lean_st_ref_take(v___y_1544_);
                    v_cache_1554_ = leanh::lean_ctor_get(v___x_1553_, 1);
                    v_zetaDeltaFVarIds_1555_ = leanh::lean_ctor_get(v___x_1553_, 2);
                    v_postponed_1556_ = leanh::lean_ctor_get(v___x_1553_, 3);
                    v_diag_1557_ = leanh::lean_ctor_get(v___x_1553_, 4);
                    v_isSharedCheck_1566_ = (!leanh::lean_is_exclusive(v___x_1553_)) as u8;
                    if v_isSharedCheck_1566_ == 0 {
                        v_unused_1567_ = leanh::lean_ctor_get(v___x_1553_, 0);
                        leanh::lean_dec(v_unused_1567_);
                        v___x_1559_ = v___x_1553_;
                        v_isShared_1560_ = v_isSharedCheck_1566_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1557_);
                        leanh::lean_inc(v_postponed_1556_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1555_);
                        leanh::lean_inc(v_cache_1554_);
                        leanh::lean_dec(v___x_1553_);
                        v___x_1559_ = leanh::lean_box(0);
                        v_isShared_1560_ = v_isSharedCheck_1566_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1560_ == 0 {
                    leanh::lean_ctor_set(v___x_1559_, 0, v_snd_1552_);
                    v___x_1562_ = v___x_1559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1565_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_snd_1552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_cache_1554_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1565_,
                        2,
                        v_zetaDeltaFVarIds_1555_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_postponed_1556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_diag_1557_);
                    v___x_1562_ = v_reuseFailAlloc_1565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1563_ = lean_st_ref_set(v___y_1544_, v___x_1562_);
                v___x_1564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1564_, 0, v_fst_1551_);
                return v___x_1564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg___boxed(
    mut v_e_1568_: *mut leanh::LeanObject,
    mut v___y_1569_: *mut leanh::LeanObject,
    mut v___y_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_1568_, v___y_1569_);
    leanh::lean_dec(v___y_1569_);
    return v_res_1571_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(
    mut v_e_1572_: *mut leanh::LeanObject,
    mut v___y_1573_: *mut leanh::LeanObject,
    mut v___y_1574_: *mut leanh::LeanObject,
    mut v___y_1575_: *mut leanh::LeanObject,
    mut v___y_1576_: *mut leanh::LeanObject,
    mut v___y_1577_: *mut leanh::LeanObject,
    mut v___y_1578_: *mut leanh::LeanObject,
    mut v___y_1579_: *mut leanh::LeanObject,
    mut v___y_1580_: *mut leanh::LeanObject,
    mut v___y_1581_: *mut leanh::LeanObject,
    mut v___y_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_e_1572_, v___y_1580_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___boxed(
    mut v_e_1585_: *mut leanh::LeanObject,
    mut v___y_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
    mut v___y_1591_: *mut leanh::LeanObject,
    mut v___y_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0(v_e_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
    leanh::lean_dec(v___y_1595_);
    leanh::lean_dec_ref(v___y_1594_);
    leanh::lean_dec(v___y_1593_);
    leanh::lean_dec_ref(v___y_1592_);
    leanh::lean_dec(v___y_1591_);
    leanh::lean_dec_ref(v___y_1590_);
    leanh::lean_dec(v___y_1589_);
    leanh::lean_dec_ref(v___y_1588_);
    leanh::lean_dec(v___y_1587_);
    leanh::lean_dec(v___y_1586_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v_mctx_1599_: *mut leanh::LeanObject,
    mut v_cache_1600_: *mut leanh::LeanObject,
    mut v_a_x3f_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v_unused_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1603_ = lean_st_ref_take(v___y_1598_);
                v_zetaDeltaFVarIds_1604_ = leanh::lean_ctor_get(v___x_1603_, 2);
                v_postponed_1605_ = leanh::lean_ctor_get(v___x_1603_, 3);
                v_diag_1606_ = leanh::lean_ctor_get(v___x_1603_, 4);
                v_isSharedCheck_1616_ = (!leanh::lean_is_exclusive(v___x_1603_)) as u8;
                if v_isSharedCheck_1616_ == 0 {
                    v_unused_1617_ = leanh::lean_ctor_get(v___x_1603_, 1);
                    leanh::lean_dec(v_unused_1617_);
                    v_unused_1618_ = leanh::lean_ctor_get(v___x_1603_, 0);
                    leanh::lean_dec(v_unused_1618_);
                    v___x_1608_ = v___x_1603_;
                    v_isShared_1609_ = v_isSharedCheck_1616_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1606_);
                    leanh::lean_inc(v_postponed_1605_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1604_);
                    leanh::lean_dec(v___x_1603_);
                    v___x_1608_ = leanh::lean_box(0);
                    v_isShared_1609_ = v_isSharedCheck_1616_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1609_ == 0 {
                    leanh::lean_ctor_set(v___x_1608_, 1, v_cache_1600_);
                    leanh::lean_ctor_set(v___x_1608_, 0, v_mctx_1599_);
                    v___x_1611_ = v___x_1608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_mctx_1599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_cache_1600_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1615_,
                        2,
                        v_zetaDeltaFVarIds_1604_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_postponed_1605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_diag_1606_);
                    v___x_1611_ = v_reuseFailAlloc_1615_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1612_ = lean_st_ref_set(v___y_1598_, v___x_1611_);
                v___x_1613_ = leanh::lean_box(0);
                v___x_1614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1614_, 0, v___x_1613_);
                return v___x_1614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0___boxed(
    mut v___y_1619_: *mut leanh::LeanObject,
    mut v_mctx_1620_: *mut leanh::LeanObject,
    mut v_cache_1621_: *mut leanh::LeanObject,
    mut v_a_x3f_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_1619_, v_mctx_1620_, v_cache_1621_, v_a_x3f_1622_);
    leanh::lean_dec(v_a_x3f_1622_);
    leanh::lean_dec(v___y_1619_);
    return v_res_1624_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(
    mut v_x_1625_: *mut leanh::LeanObject,
    mut v___y_1626_: *mut leanh::LeanObject,
    mut v___y_1627_: *mut leanh::LeanObject,
    mut v___y_1628_: *mut leanh::LeanObject,
    mut v___y_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
    mut v___y_1633_: *mut leanh::LeanObject,
    mut v___y_1634_: *mut leanh::LeanObject,
    mut v___y_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut v_unused_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut v_a_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1664_: u8 = 0;
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_unused_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1637_ = lean_st_ref_get(v___y_1633_);
                v___x_1638_ = lean_st_ref_get(v___y_1633_);
                v_mctx_1639_ = leanh::lean_ctor_get(v___x_1637_, 0);
                leanh::lean_inc_ref(v_mctx_1639_);
                leanh::lean_dec(v___x_1637_);
                v_cache_1640_ = leanh::lean_ctor_get(v___x_1638_, 1);
                leanh::lean_inc_ref(v_cache_1640_);
                leanh::lean_dec(v___x_1638_);
                leanh::lean_inc(v___y_1635_);
                leanh::lean_inc_ref(v___y_1634_);
                leanh::lean_inc(v___y_1633_);
                leanh::lean_inc_ref(v___y_1632_);
                leanh::lean_inc(v___y_1631_);
                leanh::lean_inc_ref(v___y_1630_);
                leanh::lean_inc(v___y_1629_);
                leanh::lean_inc_ref(v___y_1628_);
                leanh::lean_inc(v___y_1627_);
                leanh::lean_inc(v___y_1626_);
                v___x_1641_ = leanh::lean_apply_11(
                    v_x_1625_,
                    v___y_1626_,
                    v___y_1627_,
                    v___y_1628_,
                    v___y_1629_,
                    v___y_1630_,
                    v___y_1631_,
                    v___y_1632_,
                    v___y_1633_,
                    v___y_1634_,
                    v___y_1635_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1641_) == 0 {
                    v_a_1642_ = leanh::lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1658_ = (!leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1658_ == 0 {
                        v___x_1644_ = v___x_1641_;
                        v_isShared_1645_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1642_);
                        leanh::lean_dec(v___x_1641_);
                        v___x_1644_ = leanh::lean_box(0);
                        v_isShared_1645_ = v_isSharedCheck_1658_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1659_ = leanh::lean_ctor_get(v___x_1641_, 0);
                    leanh::lean_inc(v_a_1659_);
                    leanh::lean_dec_ref_known(v___x_1641_, 1);
                    v___x_1660_ = leanh::lean_box(0);
                    v___x_1661_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_1633_, v_mctx_1639_, v_cache_1640_, v___x_1660_);
                    v_isSharedCheck_1668_ = (!leanh::lean_is_exclusive(v___x_1661_)) as u8;
                    if v_isSharedCheck_1668_ == 0 {
                        v_unused_1669_ = leanh::lean_ctor_get(v___x_1661_, 0);
                        leanh::lean_dec(v_unused_1669_);
                        v___x_1663_ = v___x_1661_;
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1661_);
                        v___x_1663_ = leanh::lean_box(0);
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1642_);
                if v_isShared_1645_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1644_, 1);
                    v___x_1647_ = v___x_1644_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1642_);
                    v___x_1647_ = v_reuseFailAlloc_1657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1648_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___lam__0(v___y_1633_, v_mctx_1639_, v_cache_1640_, v___x_1647_);
                leanh::lean_dec_ref(v___x_1647_);
                v_isSharedCheck_1655_ = (!leanh::lean_is_exclusive(v___x_1648_)) as u8;
                if v_isSharedCheck_1655_ == 0 {
                    v_unused_1656_ = leanh::lean_ctor_get(v___x_1648_, 0);
                    leanh::lean_dec(v_unused_1656_);
                    v___x_1650_ = v___x_1648_;
                    v_isShared_1651_ = v_isSharedCheck_1655_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1648_);
                    v___x_1650_ = leanh::lean_box(0);
                    v_isShared_1651_ = v_isSharedCheck_1655_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1651_ == 0 {
                    leanh::lean_ctor_set(v___x_1650_, 0, v_a_1642_);
                    v___x_1653_ = v___x_1650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1642_);
                    v___x_1653_ = v_reuseFailAlloc_1654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1653_;
            }
            5 => {
                if v_isShared_1664_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1663_, 1);
                    leanh::lean_ctor_set(v___x_1663_, 0, v_a_1659_);
                    v___x_1666_ = v___x_1663_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1659_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg___boxed(
    mut v_x_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
    leanh::lean_dec(v___y_1680_);
    leanh::lean_dec_ref(v___y_1679_);
    leanh::lean_dec(v___y_1678_);
    leanh::lean_dec_ref(v___y_1677_);
    leanh::lean_dec(v___y_1676_);
    leanh::lean_dec_ref(v___y_1675_);
    leanh::lean_dec(v___y_1674_);
    leanh::lean_dec_ref(v___y_1673_);
    leanh::lean_dec(v___y_1672_);
    leanh::lean_dec(v___y_1671_);
    return v_res_1682_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(
    mut v_00_u03b1_1683_: *mut leanh::LeanObject,
    mut v_x_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    return v___x_1696_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___boxed(
    mut v_00_u03b1_1697_: *mut leanh::LeanObject,
    mut v_x_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1(v_00_u03b1_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
    leanh::lean_dec(v___y_1708_);
    leanh::lean_dec_ref(v___y_1707_);
    leanh::lean_dec(v___y_1706_);
    leanh::lean_dec_ref(v___y_1705_);
    leanh::lean_dec(v___y_1704_);
    leanh::lean_dec_ref(v___y_1703_);
    leanh::lean_dec(v___y_1702_);
    leanh::lean_dec_ref(v___y_1701_);
    leanh::lean_dec(v___y_1700_);
    leanh::lean_dec(v___y_1699_);
    return v_res_1710_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(
    mut v_mvarId_1713_: *mut leanh::LeanObject,
    mut v_e_1714_: *mut leanh::LeanObject,
    mut v_toGoalState_1715_: *mut leanh::LeanObject,
    mut v___y_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
    mut v___y_1720_: *mut leanh::LeanObject,
    mut v___y_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
    mut v___y_1723_: *mut leanh::LeanObject,
    mut v___y_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_1745_: u8 = 0;
    let mut v_nextIdx_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut v_a_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_reuseFailAlloc_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_unused_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_a_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1817_: u8 = 0;
    let mut v_a_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v_a_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1829_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1727_ = l_Lean_MVarId_getTag(
                    v_mvarId_1713_,
                    v___y_1722_,
                    v___y_1723_,
                    v___y_1724_,
                    v___y_1725_,
                );
                if leanh::lean_obj_tag(v___x_1727_) == 0 {
                    v_a_1728_ = leanh::lean_ctor_get(v___x_1727_, 0);
                    leanh::lean_inc(v_a_1728_);
                    leanh::lean_dec_ref_known(v___x_1727_, 1);
                    v___x_1729_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1720_);
                    if leanh::lean_obj_tag(v___x_1729_) == 0 {
                        v_a_1730_ = leanh::lean_ctor_get(v___x_1729_, 0);
                        leanh::lean_inc(v_a_1730_);
                        leanh::lean_dec_ref_known(v___x_1729_, 1);
                        leanh::lean_inc_ref(v_e_1714_);
                        v___x_1731_ = l_Lean_mkNot(v_e_1714_);
                        v___x_1732_ =
                            l_Lean_mkArrow(v___x_1731_, v_a_1730_, v___y_1724_, v___y_1725_);
                        if leanh::lean_obj_tag(v___x_1732_) == 0 {
                            v_a_1733_ = leanh::lean_ctor_get(v___x_1732_, 0);
                            leanh::lean_inc(v_a_1733_);
                            leanh::lean_dec_ref_known(v___x_1732_, 1);
                            v___x_1734_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_1733_,
                                v_a_1728_,
                                v___y_1722_,
                                v___y_1723_,
                                v___y_1724_,
                                v___y_1725_,
                            );
                            if leanh::lean_obj_tag(v___x_1734_) == 0 {
                                v_a_1735_ = leanh::lean_ctor_get(v___x_1734_, 0);
                                leanh::lean_inc(v_a_1735_);
                                leanh::lean_dec_ref_known(v___x_1734_, 1);
                                v___x_1736_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                    v_e_1714_,
                                    v___y_1716_,
                                );
                                leanh::lean_dec_ref(v_e_1714_);
                                if leanh::lean_obj_tag(v___x_1736_) == 0 {
                                    v_a_1737_ = leanh::lean_ctor_get(v___x_1736_, 0);
                                    leanh::lean_inc(v_a_1737_);
                                    leanh::lean_dec_ref_known(v___x_1736_, 1);
                                    v_nextDeclIdx_1738_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 0);
                                    v_enodeMap_1739_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 1);
                                    v_exprs_1740_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 2);
                                    v_parents_1741_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 3);
                                    v_congrTable_1742_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 4);
                                    v_appMap_1743_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 5);
                                    v_indicesFound_1744_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 6);
                                    v_inconsistent_1745_ = leanh::lean_ctor_get_uint8(
                                        v_toGoalState_1715_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17)
                                            as u32,
                                    );
                                    v_nextIdx_1746_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 8);
                                    v_newRawFacts_1747_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 9);
                                    v_facts_1748_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 10);
                                    v_extThms_1749_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 11);
                                    v_ematch_1750_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 12);
                                    v_inj_1751_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 13);
                                    v_split_1752_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 14);
                                    v_clean_1753_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 15);
                                    v_sstates_1754_ =
                                        leanh::lean_ctor_get(v_toGoalState_1715_, 16);
                                    v_isSharedCheck_1792_ =
                                        (!leanh::lean_is_exclusive(v_toGoalState_1715_))
                                            as u8;
                                    if v_isSharedCheck_1792_ == 0 {
                                        v_unused_1793_ =
                                            leanh::lean_ctor_get(v_toGoalState_1715_, 7);
                                        leanh::lean_dec(v_unused_1793_);
                                        v___x_1756_ = v_toGoalState_1715_;
                                        v_isShared_1757_ = v_isSharedCheck_1792_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_sstates_1754_);
                                        leanh::lean_inc(v_clean_1753_);
                                        leanh::lean_inc(v_split_1752_);
                                        leanh::lean_inc(v_inj_1751_);
                                        leanh::lean_inc(v_ematch_1750_);
                                        leanh::lean_inc(v_extThms_1749_);
                                        leanh::lean_inc(v_facts_1748_);
                                        leanh::lean_inc(v_newRawFacts_1747_);
                                        leanh::lean_inc(v_nextIdx_1746_);
                                        leanh::lean_inc(v_indicesFound_1744_);
                                        leanh::lean_inc(v_appMap_1743_);
                                        leanh::lean_inc(v_congrTable_1742_);
                                        leanh::lean_inc(v_parents_1741_);
                                        leanh::lean_inc(v_exprs_1740_);
                                        leanh::lean_inc(v_enodeMap_1739_);
                                        leanh::lean_inc(v_nextDeclIdx_1738_);
                                        leanh::lean_dec(v_toGoalState_1715_);
                                        v___x_1756_ = leanh::lean_box(0);
                                        v_isShared_1757_ = v_isSharedCheck_1792_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1735_);
                                    leanh::lean_dec_ref(v_toGoalState_1715_);
                                    v_a_1794_ = leanh::lean_ctor_get(v___x_1736_, 0);
                                    v_isSharedCheck_1801_ =
                                        (!leanh::lean_is_exclusive(v___x_1736_)) as u8;
                                    if v_isSharedCheck_1801_ == 0 {
                                        v___x_1796_ = v___x_1736_;
                                        v_isShared_1797_ = v_isSharedCheck_1801_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1794_);
                                        leanh::lean_dec(v___x_1736_);
                                        v___x_1796_ = leanh::lean_box(0);
                                        v_isShared_1797_ = v_isSharedCheck_1801_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_toGoalState_1715_);
                                leanh::lean_dec_ref(v_e_1714_);
                                v_a_1802_ = leanh::lean_ctor_get(v___x_1734_, 0);
                                v_isSharedCheck_1809_ =
                                    (!leanh::lean_is_exclusive(v___x_1734_)) as u8;
                                if v_isSharedCheck_1809_ == 0 {
                                    v___x_1804_ = v___x_1734_;
                                    v_isShared_1805_ = v_isSharedCheck_1809_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1802_);
                                    leanh::lean_dec(v___x_1734_);
                                    v___x_1804_ = leanh::lean_box(0);
                                    v_isShared_1805_ = v_isSharedCheck_1809_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1728_);
                            leanh::lean_dec_ref(v_toGoalState_1715_);
                            leanh::lean_dec_ref(v_e_1714_);
                            v_a_1810_ = leanh::lean_ctor_get(v___x_1732_, 0);
                            v_isSharedCheck_1817_ =
                                (!leanh::lean_is_exclusive(v___x_1732_)) as u8;
                            if v_isSharedCheck_1817_ == 0 {
                                v___x_1812_ = v___x_1732_;
                                v_isShared_1813_ = v_isSharedCheck_1817_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1810_);
                                leanh::lean_dec(v___x_1732_);
                                v___x_1812_ = leanh::lean_box(0);
                                v_isShared_1813_ = v_isSharedCheck_1817_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1728_);
                        leanh::lean_dec_ref(v_toGoalState_1715_);
                        leanh::lean_dec_ref(v_e_1714_);
                        v_a_1818_ = leanh::lean_ctor_get(v___x_1729_, 0);
                        v_isSharedCheck_1825_ =
                            (!leanh::lean_is_exclusive(v___x_1729_)) as u8;
                        if v_isSharedCheck_1825_ == 0 {
                            v___x_1820_ = v___x_1729_;
                            v_isShared_1821_ = v_isSharedCheck_1825_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1818_);
                            leanh::lean_dec(v___x_1729_);
                            v___x_1820_ = leanh::lean_box(0);
                            v_isShared_1821_ = v_isSharedCheck_1825_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_toGoalState_1715_);
                    leanh::lean_dec_ref(v_e_1714_);
                    v_a_1826_ = leanh::lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1833_ = (!leanh::lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1833_ == 0 {
                        v___x_1828_ = v___x_1727_;
                        v_isShared_1829_ = v_isSharedCheck_1833_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1826_);
                        leanh::lean_dec(v___x_1727_);
                        v___x_1828_ = leanh::lean_box(0);
                        v_isShared_1829_ = v_isSharedCheck_1833_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1758_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___closed__0;
                if v_isShared_1757_ == 0 {
                    leanh::lean_ctor_set(v___x_1756_, 7, v___x_1758_);
                    v___x_1760_ = v___x_1756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_nextDeclIdx_1738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_enodeMap_1739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_exprs_1740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_parents_1741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_congrTable_1742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 5, v_appMap_1743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 6, v_indicesFound_1744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 7, v___x_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 8, v_nextIdx_1746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 9, v_newRawFacts_1747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 10, v_facts_1748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 11, v_extThms_1749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 12, v_ematch_1750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 13, v_inj_1751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 14, v_split_1752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 15, v_clean_1753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 16, v_sstates_1754_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1791_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_1745_,
                    );
                    v___x_1760_ = v_reuseFailAlloc_1791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1761_ = l_Lean_Expr_mvarId_x21(v_a_1735_);
                v___x_1762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1762_, 0, v___x_1760_);
                leanh::lean_ctor_set(v___x_1762_, 1, v___x_1761_);
                v___x_1763_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_solve(
                    v___x_1762_,
                    v_a_1737_,
                    v___y_1717_,
                    v___y_1718_,
                    v___y_1719_,
                    v___y_1720_,
                    v___y_1721_,
                    v___y_1722_,
                    v___y_1723_,
                    v___y_1724_,
                    v___y_1725_,
                );
                if leanh::lean_obj_tag(v___x_1763_) == 0 {
                    v_a_1764_ = leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1782_ = (!leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1782_ == 0 {
                        v___x_1766_ = v___x_1763_;
                        v_isShared_1767_ = v_isSharedCheck_1782_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1764_);
                        leanh::lean_dec(v___x_1763_);
                        v___x_1766_ = leanh::lean_box(0);
                        v_isShared_1767_ = v_isSharedCheck_1782_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1735_);
                    v_a_1783_ = leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1790_ = (!leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1790_ == 0 {
                        v___x_1785_ = v___x_1763_;
                        v_isShared_1786_ = v_isSharedCheck_1790_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1783_);
                        leanh::lean_dec(v___x_1763_);
                        v___x_1785_ = leanh::lean_box(0);
                        v_isShared_1786_ = v_isSharedCheck_1790_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_1764_) == 0 {
                    leanh::lean_del_object(v___x_1766_);
                    v___x_1768_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__0___redArg(v_a_1735_, v___y_1723_);
                    v_a_1769_ = leanh::lean_ctor_get(v___x_1768_, 0);
                    v_isSharedCheck_1777_ = (!leanh::lean_is_exclusive(v___x_1768_)) as u8;
                    if v_isSharedCheck_1777_ == 0 {
                        v___x_1771_ = v___x_1768_;
                        v_isShared_1772_ = v_isSharedCheck_1777_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1769_);
                        leanh::lean_dec(v___x_1768_);
                        v___x_1771_ = leanh::lean_box(0);
                        v_isShared_1772_ = v_isSharedCheck_1777_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_1764_, 1);
                    leanh::lean_dec(v_a_1735_);
                    v___x_1778_ = leanh::lean_box(0);
                    if v_isShared_1767_ == 0 {
                        leanh::lean_ctor_set(v___x_1766_, 0, v___x_1778_);
                        v___x_1780_ = v___x_1766_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1781_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
                        v___x_1780_ = v_reuseFailAlloc_1781_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1773_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1773_, 0, v_a_1769_);
                if v_isShared_1772_ == 0 {
                    leanh::lean_ctor_set(v___x_1771_, 0, v___x_1773_);
                    v___x_1775_ = v___x_1771_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
                    v___x_1775_ = v_reuseFailAlloc_1776_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1775_;
            }
            6 => {
                return v___x_1780_;
            }
            7 => {
                if v_isShared_1786_ == 0 {
                    v___x_1788_ = v___x_1785_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
                    v___x_1788_ = v_reuseFailAlloc_1789_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1788_;
            }
            9 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1799_;
            }
            11 => {
                if v_isShared_1805_ == 0 {
                    v___x_1807_ = v___x_1804_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1807_;
            }
            13 => {
                if v_isShared_1813_ == 0 {
                    v___x_1815_ = v___x_1812_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
                    v___x_1815_ = v_reuseFailAlloc_1816_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1815_;
            }
            15 => {
                if v_isShared_1821_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
                    v___x_1823_ = v_reuseFailAlloc_1824_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1823_;
            }
            17 => {
                if v_isShared_1829_ == 0 {
                    v___x_1831_ = v___x_1828_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
                    v___x_1831_ = v_reuseFailAlloc_1832_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed(
    mut v_mvarId_1834_: *mut leanh::LeanObject,
    mut v_e_1835_: *mut leanh::LeanObject,
    mut v_toGoalState_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0(
            v_mvarId_1834_,
            v_e_1835_,
            v_toGoalState_1836_,
            v___y_1837_,
            v___y_1838_,
            v___y_1839_,
            v___y_1840_,
            v___y_1841_,
            v___y_1842_,
            v___y_1843_,
            v___y_1844_,
            v___y_1845_,
            v___y_1846_,
        );
    leanh::lean_dec(v___y_1846_);
    leanh::lean_dec_ref(v___y_1845_);
    leanh::lean_dec(v___y_1844_);
    leanh::lean_dec_ref(v___y_1843_);
    leanh::lean_dec(v___y_1842_);
    leanh::lean_dec_ref(v___y_1841_);
    leanh::lean_dec(v___y_1840_);
    leanh::lean_dec_ref(v___y_1839_);
    leanh::lean_dec(v___y_1838_);
    leanh::lean_dec(v___y_1837_);
    return v_res_1848_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(
    mut v_msgData_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = lean_st_ref_get(v___y_1853_);
    v_env_1856_ = leanh::lean_ctor_get(v___x_1855_, 0);
    leanh::lean_inc_ref(v_env_1856_);
    leanh::lean_dec(v___x_1855_);
    v___x_1857_ = lean_st_ref_get(v___y_1851_);
    v_mctx_1858_ = leanh::lean_ctor_get(v___x_1857_, 0);
    leanh::lean_inc_ref(v_mctx_1858_);
    leanh::lean_dec(v___x_1857_);
    v_lctx_1859_ = leanh::lean_ctor_get(v___y_1850_, 2);
    v_options_1860_ = leanh::lean_ctor_get(v___y_1852_, 2);
    leanh::lean_inc_ref(v_options_1860_);
    leanh::lean_inc_ref(v_lctx_1859_);
    v___x_1861_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1861_, 0, v_env_1856_);
    leanh::lean_ctor_set(v___x_1861_, 1, v_mctx_1858_);
    leanh::lean_ctor_set(v___x_1861_, 2, v_lctx_1859_);
    leanh::lean_ctor_set(v___x_1861_, 3, v_options_1860_);
    v___x_1862_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    leanh::lean_ctor_set(v___x_1862_, 1, v_msgData_1849_);
    v___x_1863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2___boxed(
    mut v_msgData_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msgData_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
    leanh::lean_dec(v___y_1868_);
    leanh::lean_dec_ref(v___y_1867_);
    leanh::lean_dec(v___y_1866_);
    leanh::lean_dec_ref(v___y_1865_);
    return v_res_1870_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: f64 = 0.0;
    v___x_1871_ = leanh::lean_unsigned_to_nat(0);
    v___x_1872_ = lean_float_of_nat(v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(
    mut v_cls_1876_: *mut leanh::LeanObject,
    mut v_msg_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v_tid_1902_: u64 = 0;
    let mut v_traces_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: f64 = 0.0;
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1883_ = leanh::lean_ctor_get(v___y_1880_, 5);
                v___x_1884_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2_spec__2(v_msg_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
                v_a_1885_ = leanh::lean_ctor_get(v___x_1884_, 0);
                v_isSharedCheck_1929_ = (!leanh::lean_is_exclusive(v___x_1884_)) as u8;
                if v_isSharedCheck_1929_ == 0 {
                    v___x_1887_ = v___x_1884_;
                    v_isShared_1888_ = v_isSharedCheck_1929_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1885_);
                    leanh::lean_dec(v___x_1884_);
                    v___x_1887_ = leanh::lean_box(0);
                    v_isShared_1888_ = v_isSharedCheck_1929_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1889_ = lean_st_ref_take(v___y_1881_);
                v_traceState_1890_ = leanh::lean_ctor_get(v___x_1889_, 4);
                v_env_1891_ = leanh::lean_ctor_get(v___x_1889_, 0);
                v_nextMacroScope_1892_ = leanh::lean_ctor_get(v___x_1889_, 1);
                v_ngen_1893_ = leanh::lean_ctor_get(v___x_1889_, 2);
                v_auxDeclNGen_1894_ = leanh::lean_ctor_get(v___x_1889_, 3);
                v_cache_1895_ = leanh::lean_ctor_get(v___x_1889_, 5);
                v_messages_1896_ = leanh::lean_ctor_get(v___x_1889_, 6);
                v_infoState_1897_ = leanh::lean_ctor_get(v___x_1889_, 7);
                v_snapshotTasks_1898_ = leanh::lean_ctor_get(v___x_1889_, 8);
                v_isSharedCheck_1928_ = (!leanh::lean_is_exclusive(v___x_1889_)) as u8;
                if v_isSharedCheck_1928_ == 0 {
                    v___x_1900_ = v___x_1889_;
                    v_isShared_1901_ = v_isSharedCheck_1928_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1898_);
                    leanh::lean_inc(v_infoState_1897_);
                    leanh::lean_inc(v_messages_1896_);
                    leanh::lean_inc(v_cache_1895_);
                    leanh::lean_inc(v_traceState_1890_);
                    leanh::lean_inc(v_auxDeclNGen_1894_);
                    leanh::lean_inc(v_ngen_1893_);
                    leanh::lean_inc(v_nextMacroScope_1892_);
                    leanh::lean_inc(v_env_1891_);
                    leanh::lean_dec(v___x_1889_);
                    v___x_1900_ = leanh::lean_box(0);
                    v_isShared_1901_ = v_isSharedCheck_1928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1902_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1890_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1903_ = leanh::lean_ctor_get(v_traceState_1890_, 0);
                v_isSharedCheck_1927_ =
                    (!leanh::lean_is_exclusive(v_traceState_1890_)) as u8;
                if v_isSharedCheck_1927_ == 0 {
                    v___x_1905_ = v_traceState_1890_;
                    v_isShared_1906_ = v_isSharedCheck_1927_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1903_);
                    leanh::lean_dec(v_traceState_1890_);
                    v___x_1905_ = leanh::lean_box(0);
                    v_isShared_1906_ = v_isSharedCheck_1927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1907_ = leanh::lean_box(0);
                v___x_1908_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__0);
                v___x_1909_ = 0;
                v___x_1910_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__1;
                v___x_1911_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1911_, 0, v_cls_1876_);
                leanh::lean_ctor_set(v___x_1911_, 1, v___x_1907_);
                leanh::lean_ctor_set(v___x_1911_, 2, v___x_1910_);
                leanh::lean_ctor_set_float(
                    v___x_1911_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1908_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1911_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1908_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1911_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1909_,
                );
                v___x_1912_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___closed__2;
                v___x_1913_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1913_, 0, v___x_1911_);
                leanh::lean_ctor_set(v___x_1913_, 1, v_a_1885_);
                leanh::lean_ctor_set(v___x_1913_, 2, v___x_1912_);
                leanh::lean_inc(v_ref_1883_);
                v___x_1914_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1914_, 0, v_ref_1883_);
                leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                v___x_1915_ = l_Lean_PersistentArray_push___redArg(v_traces_1903_, v___x_1914_);
                if v_isShared_1906_ == 0 {
                    leanh::lean_ctor_set(v___x_1905_, 0, v___x_1915_);
                    v___x_1917_ = v___x_1905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1915_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1926_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1902_,
                    );
                    v___x_1917_ = v_reuseFailAlloc_1926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1901_ == 0 {
                    leanh::lean_ctor_set(v___x_1900_, 4, v___x_1917_);
                    v___x_1919_ = v___x_1900_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1925_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_env_1891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_nextMacroScope_1892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_ngen_1893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_auxDeclNGen_1894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 4, v___x_1917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 5, v_cache_1895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 6, v_messages_1896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 7, v_infoState_1897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 8, v_snapshotTasks_1898_);
                    v___x_1919_ = v_reuseFailAlloc_1925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1920_ = lean_st_ref_set(v___y_1881_, v___x_1919_);
                v___x_1921_ = leanh::lean_box(0);
                if v_isShared_1888_ == 0 {
                    leanh::lean_ctor_set(v___x_1887_, 0, v___x_1921_);
                    v___x_1923_ = v___x_1887_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
                    v___x_1923_ = v_reuseFailAlloc_1924_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg___boxed(
    mut v_cls_1930_: *mut leanh::LeanObject,
    mut v_msg_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
    mut v___y_1935_: *mut leanh::LeanObject,
    mut v___y_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_1930_, v_msg_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
    leanh::lean_dec(v___y_1935_);
    leanh::lean_dec_ref(v___y_1934_);
    leanh::lean_dec(v___y_1933_);
    leanh::lean_dec_ref(v___y_1932_);
    return v_res_1937_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = leanh::lean_box(0);
    v___x_1946_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__3;
    v___x_1947_ = l_Lean_mkConst(v___x_1946_, v___x_1945_);
    return v___x_1947_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8;
    v___x_1959_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10;
    v___x_1960_ = l_Lean_Name_append(v___x_1959_, v___x_1958_);
    return v___x_1960_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14()
-> *mut leanh::LeanObject {
    let mut v_cls_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_1966_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13;
    v___x_1967_ =
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__10;
    v___x_1968_ = l_Lean_Name_append(v___x_1967_, v_cls_1966_);
    return v___x_1968_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(
    mut v_e_1969_: *mut leanh::LeanObject,
    mut v_a_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
    mut v_a_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
    mut v_a_1976_: *mut leanh::LeanObject,
    mut v_a_1977_: *mut leanh::LeanObject,
    mut v_a_1978_: *mut leanh::LeanObject,
    mut v_a_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut v_unused_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut v_a_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2018_: u8 = 0;
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2022_: u8 = 0;
    let mut v_config_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorRefs_x3f_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportMVarIssue_2028_: u8 = 0;
    let mut v_splitSource_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiagSource_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_symPrios_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2033_: u8 = 0;
    let mut v_ematchDiag_2034_: u8 = 0;
    let mut v_trace_2035_: u8 = 0;
    let mut v_markInstances_2036_: u8 = 0;
    let mut v_lax_2037_: u8 = 0;
    let mut v_suggestions_2038_: u8 = 0;
    let mut v_locals_2039_: u8 = 0;
    let mut v_splits_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_genLocal_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchEqs_2045_: u8 = 0;
    let mut v_splitMatch_2046_: u8 = 0;
    let mut v_splitIte_2047_: u8 = 0;
    let mut v_splitIndPred_2048_: u8 = 0;
    let mut v_splitImp_2049_: u8 = 0;
    let mut v_canonHeartbeats_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_2051_: u8 = 0;
    let mut v_extAll_2052_: u8 = 0;
    let mut v_etaStruct_2053_: u8 = 0;
    let mut v_funext_2054_: u8 = 0;
    let mut v_lookahead_2055_: u8 = 0;
    let mut v_verbose_2056_: u8 = 0;
    let mut v_clean_2057_: u8 = 0;
    let mut v_mbtc_2058_: u8 = 0;
    let mut v_zetaDelta_2059_: u8 = 0;
    let mut v_zeta_2060_: u8 = 0;
    let mut v_ring_2061_: u8 = 0;
    let mut v_ringSteps_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringMaxDegree_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linarith_2064_: u8 = 0;
    let mut v_lia_2065_: u8 = 0;
    let mut v_ac_2066_: u8 = 0;
    let mut v_acSteps_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exp_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractProof_2069_: u8 = 0;
    let mut v_inj_2070_: u8 = 0;
    let mut v_order_2071_: u8 = 0;
    let mut v_min_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_detailed_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_useSorry_2074_: u8 = 0;
    let mut v_revert_2075_: u8 = 0;
    let mut v_funCC_2076_: u8 = 0;
    let mut v_reducible_2077_: u8 = 0;
    let mut v_maxSuggestions_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v_options_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2104_: u8 = 0;
    let mut v_val_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v___x_2121_: u8 = 0;
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_a_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2145_: u8 = 0;
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_a_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_2023_ = leanh::lean_ctor_get(v_a_1972_, 2);
                v_options_2024_ = leanh::lean_ctor_get(v_a_1978_, 2);
                v_simp_2025_ = leanh::lean_ctor_get(v_a_1972_, 0);
                v_simpMethods_2026_ = leanh::lean_ctor_get(v_a_1972_, 1);
                v_anchorRefs_x3f_2027_ = leanh::lean_ctor_get(v_a_1972_, 3);
                v_reportMVarIssue_2028_ = leanh::lean_ctor_get_uint8(
                    v_a_1972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_splitSource_2029_ = leanh::lean_ctor_get(v_a_1972_, 4);
                v_ematchDiagSource_2030_ = leanh::lean_ctor_get(v_a_1972_, 5);
                v_symPrios_2031_ = leanh::lean_ctor_get(v_a_1972_, 6);
                v_extensions_2032_ = leanh::lean_ctor_get(v_a_1972_, 7);
                v_debug_2033_ = leanh::lean_ctor_get_uint8(
                    v_a_1972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_ematchDiag_2034_ = leanh::lean_ctor_get_uint8(
                    v_a_1972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_trace_2035_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_markInstances_2036_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_lax_2037_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 2) as u32,
                );
                v_suggestions_2038_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 3) as u32,
                );
                v_locals_2039_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 4) as u32,
                );
                v_splits_2040_ = leanh::lean_ctor_get(v_config_2023_, 0);
                v_ematch_2041_ = leanh::lean_ctor_get(v_config_2023_, 1);
                v_gen_2042_ = leanh::lean_ctor_get(v_config_2023_, 2);
                v_genLocal_2043_ = leanh::lean_ctor_get(v_config_2023_, 3);
                v_instances_2044_ = leanh::lean_ctor_get(v_config_2023_, 4);
                v_matchEqs_2045_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 5) as u32,
                );
                v_splitMatch_2046_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 6) as u32,
                );
                v_splitIte_2047_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 7) as u32,
                );
                v_splitIndPred_2048_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 8) as u32,
                );
                v_splitImp_2049_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 9) as u32,
                );
                v_canonHeartbeats_2050_ = leanh::lean_ctor_get(v_config_2023_, 5);
                v_ext_2051_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 10) as u32,
                );
                v_extAll_2052_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 11) as u32,
                );
                v_etaStruct_2053_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 12) as u32,
                );
                v_funext_2054_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 13) as u32,
                );
                v_lookahead_2055_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 14) as u32,
                );
                v_verbose_2056_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 15) as u32,
                );
                v_clean_2057_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 16) as u32,
                );
                v_mbtc_2058_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 18) as u32,
                );
                v_zetaDelta_2059_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 19) as u32,
                );
                v_zeta_2060_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 20) as u32,
                );
                v_ring_2061_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 21) as u32,
                );
                v_ringSteps_2062_ = leanh::lean_ctor_get(v_config_2023_, 6);
                v_ringMaxDegree_2063_ = leanh::lean_ctor_get(v_config_2023_, 7);
                v_linarith_2064_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 22) as u32,
                );
                v_lia_2065_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 23) as u32,
                );
                v_ac_2066_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 24) as u32,
                );
                v_acSteps_2067_ = leanh::lean_ctor_get(v_config_2023_, 8);
                v_exp_2068_ = leanh::lean_ctor_get(v_config_2023_, 9);
                v_abstractProof_2069_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 25) as u32,
                );
                v_inj_2070_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 26) as u32,
                );
                v_order_2071_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 27) as u32,
                );
                v_min_2072_ = leanh::lean_ctor_get(v_config_2023_, 10);
                v_detailed_2073_ = leanh::lean_ctor_get(v_config_2023_, 11);
                v_useSorry_2074_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 28) as u32,
                );
                v_revert_2075_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 29) as u32,
                );
                v_funCC_2076_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 30) as u32,
                );
                v_reducible_2077_ = leanh::lean_ctor_get_uint8(
                    v_config_2023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 31) as u32,
                );
                v_maxSuggestions_2078_ = leanh::lean_ctor_get(v_config_2023_, 12);
                v_inheritedTraceOptions_2079_ = leanh::lean_ctor_get(v_a_1978_, 13);
                v_hasTrace_2080_ = leanh::lean_ctor_get_uint8(
                    v_options_2024_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_2081_ = 1;
                leanh::lean_inc(v_maxSuggestions_2078_);
                leanh::lean_inc(v_detailed_2073_);
                leanh::lean_inc(v_min_2072_);
                leanh::lean_inc(v_exp_2068_);
                leanh::lean_inc(v_acSteps_2067_);
                leanh::lean_inc(v_ringMaxDegree_2063_);
                leanh::lean_inc(v_ringSteps_2062_);
                leanh::lean_inc(v_canonHeartbeats_2050_);
                leanh::lean_inc(v_instances_2044_);
                leanh::lean_inc(v_genLocal_2043_);
                leanh::lean_inc(v_gen_2042_);
                leanh::lean_inc(v_ematch_2041_);
                leanh::lean_inc(v_splits_2040_);
                v___x_2082_ = leanh::lean_alloc_ctor(0, 13, (32) as u32);
                leanh::lean_ctor_set(v___x_2082_, 0, v_splits_2040_);
                leanh::lean_ctor_set(v___x_2082_, 1, v_ematch_2041_);
                leanh::lean_ctor_set(v___x_2082_, 2, v_gen_2042_);
                leanh::lean_ctor_set(v___x_2082_, 3, v_genLocal_2043_);
                leanh::lean_ctor_set(v___x_2082_, 4, v_instances_2044_);
                leanh::lean_ctor_set(v___x_2082_, 5, v_canonHeartbeats_2050_);
                leanh::lean_ctor_set(v___x_2082_, 6, v_ringSteps_2062_);
                leanh::lean_ctor_set(v___x_2082_, 7, v_ringMaxDegree_2063_);
                leanh::lean_ctor_set(v___x_2082_, 8, v_acSteps_2067_);
                leanh::lean_ctor_set(v___x_2082_, 9, v_exp_2068_);
                leanh::lean_ctor_set(v___x_2082_, 10, v_min_2072_);
                leanh::lean_ctor_set(v___x_2082_, 11, v_detailed_2073_);
                leanh::lean_ctor_set(v___x_2082_, 12, v_maxSuggestions_2078_);
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                    v_trace_2035_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                    v_markInstances_2036_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 2) as u32,
                    v_lax_2037_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 3) as u32,
                    v_suggestions_2038_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 4) as u32,
                    v_locals_2039_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 5) as u32,
                    v_matchEqs_2045_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 6) as u32,
                    v_splitMatch_2046_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 7) as u32,
                    v_splitIte_2047_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 8) as u32,
                    v_splitIndPred_2048_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 9) as u32,
                    v_splitImp_2049_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 10) as u32,
                    v_ext_2051_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 11) as u32,
                    v_extAll_2052_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 12) as u32,
                    v_etaStruct_2053_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 13) as u32,
                    v_funext_2054_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 14) as u32,
                    v_lookahead_2055_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 15) as u32,
                    v_verbose_2056_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 16) as u32,
                    v_clean_2057_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 17) as u32,
                    v___x_2081_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 18) as u32,
                    v_mbtc_2058_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 19) as u32,
                    v_zetaDelta_2059_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 20) as u32,
                    v_zeta_2060_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 21) as u32,
                    v_ring_2061_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 22) as u32,
                    v_linarith_2064_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 23) as u32,
                    v_lia_2065_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 24) as u32,
                    v_ac_2066_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 25) as u32,
                    v_abstractProof_2069_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 26) as u32,
                    v_inj_2070_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 27) as u32,
                    v_order_2071_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 28) as u32,
                    v_useSorry_2074_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 29) as u32,
                    v_revert_2075_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 30) as u32,
                    v_funCC_2076_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2082_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 31) as u32,
                    v_reducible_2077_,
                );
                leanh::lean_inc_ref(v_extensions_2032_);
                leanh::lean_inc_ref(v_symPrios_2031_);
                leanh::lean_inc(v_ematchDiagSource_2030_);
                leanh::lean_inc(v_splitSource_2029_);
                leanh::lean_inc(v_anchorRefs_x3f_2027_);
                leanh::lean_inc_ref(v_simpMethods_2026_);
                leanh::lean_inc_ref(v_simp_2025_);
                v___x_2135_ = leanh::lean_alloc_ctor(0, 8, (4) as u32);
                leanh::lean_ctor_set(v___x_2135_, 0, v_simp_2025_);
                leanh::lean_ctor_set(v___x_2135_, 1, v_simpMethods_2026_);
                leanh::lean_ctor_set(v___x_2135_, 2, v___x_2082_);
                leanh::lean_ctor_set(v___x_2135_, 3, v_anchorRefs_x3f_2027_);
                leanh::lean_ctor_set(v___x_2135_, 4, v_splitSource_2029_);
                leanh::lean_ctor_set(v___x_2135_, 5, v_ematchDiagSource_2030_);
                leanh::lean_ctor_set(v___x_2135_, 6, v_symPrios_2031_);
                leanh::lean_ctor_set(v___x_2135_, 7, v_extensions_2032_);
                leanh::lean_ctor_set_uint8(
                    v___x_2135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    v___x_2081_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                    v_reportMVarIssue_2028_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                    v_debug_2033_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                    v_ematchDiag_2034_,
                );
                if v_hasTrace_2080_ == 0 {
                    v___y_2084_ = v_a_1970_;
                    v___y_2085_ = v_a_1971_;
                    v___y_2086_ = v___x_2135_;
                    v___y_2087_ = v_a_1973_;
                    v___y_2088_ = v_a_1974_;
                    v___y_2089_ = v_a_1975_;
                    v___y_2090_ = v_a_1976_;
                    v___y_2091_ = v_a_1977_;
                    v___y_2092_ = v_a_1978_;
                    v___y_2093_ = v_a_1979_;
                    state = 8;
                    continue;
                } else {
                    v_cls_2136_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__13;
                    v___x_2137_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__14);
                    v___x_2138_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2079_,
                        v_options_2024_,
                        v___x_2137_,
                    );
                    if v___x_2138_ == 0 {
                        v___y_2084_ = v_a_1970_;
                        v___y_2085_ = v_a_1971_;
                        v___y_2086_ = v___x_2135_;
                        v___y_2087_ = v_a_1973_;
                        v___y_2088_ = v_a_1974_;
                        v___y_2089_ = v_a_1975_;
                        v___y_2090_ = v_a_1976_;
                        v___y_2091_ = v_a_1977_;
                        v___y_2092_ = v_a_1978_;
                        v___y_2093_ = v_a_1979_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2139_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_1970_,
                            v_a_1971_,
                            v___x_2135_,
                            v_a_1973_,
                            v_a_1974_,
                            v_a_1975_,
                            v_a_1976_,
                            v_a_1977_,
                            v_a_1978_,
                            v_a_1979_,
                        );
                        if leanh::lean_obj_tag(v___x_2139_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2139_, 1);
                            leanh::lean_inc_ref(v_e_1969_);
                            v___x_2140_ = l_Lean_MessageData_ofExpr(v_e_1969_);
                            v___x_2141_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_2136_, v___x_2140_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
                            if leanh::lean_obj_tag(v___x_2141_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2141_, 1);
                                v___y_2084_ = v_a_1970_;
                                v___y_2085_ = v_a_1971_;
                                v___y_2086_ = v___x_2135_;
                                v___y_2087_ = v_a_1973_;
                                v___y_2088_ = v_a_1974_;
                                v___y_2089_ = v_a_1975_;
                                v___y_2090_ = v_a_1976_;
                                v___y_2091_ = v_a_1977_;
                                v___y_2092_ = v_a_1978_;
                                v___y_2093_ = v_a_1979_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v___x_2135_, 8);
                                leanh::lean_dec_ref(v_e_1969_);
                                v_a_2142_ = leanh::lean_ctor_get(v___x_2141_, 0);
                                v_isSharedCheck_2149_ =
                                    (!leanh::lean_is_exclusive(v___x_2141_)) as u8;
                                if v_isSharedCheck_2149_ == 0 {
                                    v___x_2144_ = v___x_2141_;
                                    v_isShared_2145_ = v_isSharedCheck_2149_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2142_);
                                    leanh::lean_dec(v___x_2141_);
                                    v___x_2144_ = leanh::lean_box(0);
                                    v_isShared_2145_ = v_isSharedCheck_2149_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_2135_, 8);
                            leanh::lean_dec_ref(v_e_1969_);
                            v_a_2150_ = leanh::lean_ctor_get(v___x_2139_, 0);
                            v_isSharedCheck_2157_ =
                                (!leanh::lean_is_exclusive(v___x_2139_)) as u8;
                            if v_isSharedCheck_2157_ == 0 {
                                v___x_2152_ = v___x_2139_;
                                v_isShared_2153_ = v_isSharedCheck_2157_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2150_);
                                leanh::lean_dec(v___x_2139_);
                                v___x_2152_ = leanh::lean_box(0);
                                v_isShared_2153_ = v_isSharedCheck_2157_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1993_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__4);
                leanh::lean_inc_ref(v_e_1969_);
                v___x_1994_ = l_Lean_mkAppB(v___x_1993_, v_e_1969_, v___y_1982_);
                v___x_1995_ = l_Lean_Meta_Grind_pushEqTrue___redArg(
                    v_e_1969_,
                    v___x_1994_,
                    v___y_1983_,
                    v___y_1985_,
                    v___y_1987_,
                    v___y_1989_,
                    v___y_1990_,
                    v___y_1991_,
                    v___y_1992_,
                );
                if leanh::lean_obj_tag(v___x_1995_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1995_, 1);
                    leanh::lean_inc(v___y_1992_);
                    leanh::lean_inc_ref(v___y_1991_);
                    leanh::lean_inc(v___y_1990_);
                    leanh::lean_inc_ref(v___y_1989_);
                    leanh::lean_inc(v___y_1988_);
                    leanh::lean_inc_ref(v___y_1987_);
                    leanh::lean_inc(v___y_1986_);
                    leanh::lean_inc(v___y_1984_);
                    leanh::lean_inc(v___y_1983_);
                    v___x_1996_ = lean_grind_process_new_facts(
                        v___y_1983_,
                        v___y_1984_,
                        v___y_1985_,
                        v___y_1986_,
                        v___y_1987_,
                        v___y_1988_,
                        v___y_1989_,
                        v___y_1990_,
                        v___y_1991_,
                        v___y_1992_,
                    );
                    if leanh::lean_obj_tag(v___x_1996_) == 0 {
                        v_isSharedCheck_2005_ =
                            (!leanh::lean_is_exclusive(v___x_1996_)) as u8;
                        if v_isSharedCheck_2005_ == 0 {
                            v_unused_2006_ = leanh::lean_ctor_get(v___x_1996_, 0);
                            leanh::lean_dec(v_unused_2006_);
                            v___x_1998_ = v___x_1996_;
                            v_isShared_1999_ = v_isSharedCheck_2005_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1996_);
                            v___x_1998_ = leanh::lean_box(0);
                            v_isShared_1999_ = v_isSharedCheck_2005_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2007_ = leanh::lean_ctor_get(v___x_1996_, 0);
                        v_isSharedCheck_2014_ =
                            (!leanh::lean_is_exclusive(v___x_1996_)) as u8;
                        if v_isSharedCheck_2014_ == 0 {
                            v___x_2009_ = v___x_1996_;
                            v_isShared_2010_ = v_isSharedCheck_2014_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2007_);
                            leanh::lean_dec(v___x_1996_);
                            v___x_2009_ = leanh::lean_box(0);
                            v_isShared_2010_ = v_isSharedCheck_2014_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_1985_);
                    v_a_2015_ = leanh::lean_ctor_get(v___x_1995_, 0);
                    v_isSharedCheck_2022_ = (!leanh::lean_is_exclusive(v___x_1995_)) as u8;
                    if v_isSharedCheck_2022_ == 0 {
                        v___x_2017_ = v___x_1995_;
                        v_isShared_2018_ = v_isSharedCheck_2022_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2015_);
                        leanh::lean_dec(v___x_1995_);
                        v___x_2017_ = leanh::lean_box(0);
                        v_isShared_2018_ = v_isSharedCheck_2022_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2000_ = 1;
                v___x_2001_ = leanh::lean_box((v___x_2000_) as usize);
                if v_isShared_1999_ == 0 {
                    leanh::lean_ctor_set(v___x_1998_, 0, v___x_2001_);
                    v___x_2003_ = v___x_1998_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
                    v___x_2003_ = v_reuseFailAlloc_2004_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2003_;
            }
            4 => {
                if v_isShared_2010_ == 0 {
                    v___x_2012_ = v___x_2009_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
                    v___x_2012_ = v_reuseFailAlloc_2013_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2012_;
            }
            6 => {
                if v_isShared_2018_ == 0 {
                    v___x_2020_ = v___x_2017_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
                    v___x_2020_ = v_reuseFailAlloc_2021_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2020_;
            }
            8 => {
                v___x_2094_ = lean_st_ref_get(v___y_2084_);
                v_toGoalState_2095_ = leanh::lean_ctor_get(v___x_2094_, 0);
                leanh::lean_inc_ref(v_toGoalState_2095_);
                v_mvarId_2096_ = leanh::lean_ctor_get(v___x_2094_, 1);
                leanh::lean_inc(v_mvarId_2096_);
                leanh::lean_dec(v___x_2094_);
                leanh::lean_inc_ref(v_e_1969_);
                v___f_2097_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___lam__0___boxed as *mut core::ffi::c_void, 14, 3);
                leanh::lean_closure_set(v___f_2097_, 0, v_mvarId_2096_);
                leanh::lean_closure_set(v___f_2097_, 1, v_e_1969_);
                leanh::lean_closure_set(v___f_2097_, 2, v_toGoalState_2095_);
                v___x_2098_ = l_Lean_Meta_withoutModifyingMCtx___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__1___redArg(v___f_2097_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
                if leanh::lean_obj_tag(v___x_2098_) == 0 {
                    v_a_2099_ = leanh::lean_ctor_get(v___x_2098_, 0);
                    v_isSharedCheck_2126_ = (!leanh::lean_is_exclusive(v___x_2098_)) as u8;
                    if v_isSharedCheck_2126_ == 0 {
                        v___x_2101_ = v___x_2098_;
                        v_isShared_2102_ = v_isSharedCheck_2126_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2099_);
                        leanh::lean_dec(v___x_2098_);
                        v___x_2101_ = leanh::lean_box(0);
                        v_isShared_2102_ = v_isSharedCheck_2126_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2086_);
                    leanh::lean_dec_ref(v_e_1969_);
                    v_a_2127_ = leanh::lean_ctor_get(v___x_2098_, 0);
                    v_isSharedCheck_2134_ = (!leanh::lean_is_exclusive(v___x_2098_)) as u8;
                    if v_isSharedCheck_2134_ == 0 {
                        v___x_2129_ = v___x_2098_;
                        v_isShared_2130_ = v_isSharedCheck_2134_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2127_);
                        leanh::lean_dec(v___x_2098_);
                        v___x_2129_ = leanh::lean_box(0);
                        v_isShared_2130_ = v_isSharedCheck_2134_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                if leanh::lean_obj_tag(v_a_2099_) == 1 {
                    leanh::lean_del_object(v___x_2101_);
                    v_options_2103_ = leanh::lean_ctor_get(v___y_2092_, 2);
                    v_hasTrace_2104_ = leanh::lean_ctor_get_uint8(
                        v_options_2103_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2104_ == 0 {
                        v_val_2105_ = leanh::lean_ctor_get(v_a_2099_, 0);
                        leanh::lean_inc(v_val_2105_);
                        leanh::lean_dec_ref_known(v_a_2099_, 1);
                        v___y_1982_ = v_val_2105_;
                        v___y_1983_ = v___y_2084_;
                        v___y_1984_ = v___y_2085_;
                        v___y_1985_ = v___y_2086_;
                        v___y_1986_ = v___y_2087_;
                        v___y_1987_ = v___y_2088_;
                        v___y_1988_ = v___y_2089_;
                        v___y_1989_ = v___y_2090_;
                        v___y_1990_ = v___y_2091_;
                        v___y_1991_ = v___y_2092_;
                        v___y_1992_ = v___y_2093_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2106_ = leanh::lean_ctor_get(v_a_2099_, 0);
                        leanh::lean_inc(v_val_2106_);
                        leanh::lean_dec_ref_known(v_a_2099_, 1);
                        v_inheritedTraceOptions_2107_ =
                            leanh::lean_ctor_get(v___y_2092_, 13);
                        v___x_2108_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__8;
                        v___x_2109_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___closed__11);
                        v___x_2110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2107_,
                            v_options_2103_,
                            v___x_2109_,
                        );
                        if v___x_2110_ == 0 {
                            v___y_1982_ = v_val_2106_;
                            v___y_1983_ = v___y_2084_;
                            v___y_1984_ = v___y_2085_;
                            v___y_1985_ = v___y_2086_;
                            v___y_1986_ = v___y_2087_;
                            v___y_1987_ = v___y_2088_;
                            v___y_1988_ = v___y_2089_;
                            v___y_1989_ = v___y_2090_;
                            v___y_1990_ = v___y_2091_;
                            v___y_1991_ = v___y_2092_;
                            v___y_1992_ = v___y_2093_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc_ref(v_e_1969_);
                            v___x_2111_ = l_Lean_MessageData_ofExpr(v_e_1969_);
                            v___x_2112_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v___x_2108_, v___x_2111_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
                            if leanh::lean_obj_tag(v___x_2112_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2112_, 1);
                                v___y_1982_ = v_val_2106_;
                                v___y_1983_ = v___y_2084_;
                                v___y_1984_ = v___y_2085_;
                                v___y_1985_ = v___y_2086_;
                                v___y_1986_ = v___y_2087_;
                                v___y_1987_ = v___y_2088_;
                                v___y_1988_ = v___y_2089_;
                                v___y_1989_ = v___y_2090_;
                                v___y_1990_ = v___y_2091_;
                                v___y_1991_ = v___y_2092_;
                                v___y_1992_ = v___y_2093_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_2106_);
                                leanh::lean_dec_ref(v___y_2086_);
                                leanh::lean_dec_ref(v_e_1969_);
                                v_a_2113_ = leanh::lean_ctor_get(v___x_2112_, 0);
                                v_isSharedCheck_2120_ =
                                    (!leanh::lean_is_exclusive(v___x_2112_)) as u8;
                                if v_isSharedCheck_2120_ == 0 {
                                    v___x_2115_ = v___x_2112_;
                                    v_isShared_2116_ = v_isSharedCheck_2120_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2113_);
                                    leanh::lean_dec(v___x_2112_);
                                    v___x_2115_ = leanh::lean_box(0);
                                    v_isShared_2116_ = v_isSharedCheck_2120_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2099_);
                    leanh::lean_dec_ref(v___y_2086_);
                    leanh::lean_dec_ref(v_e_1969_);
                    v___x_2121_ = 0;
                    v___x_2122_ = leanh::lean_box((v___x_2121_) as usize);
                    if v_isShared_2102_ == 0 {
                        leanh::lean_ctor_set(v___x_2101_, 0, v___x_2122_);
                        v___x_2124_ = v___x_2101_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
                        v___x_2124_ = v_reuseFailAlloc_2125_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2116_ == 0 {
                    v___x_2118_ = v___x_2115_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
                    v___x_2118_ = v_reuseFailAlloc_2119_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2118_;
            }
            12 => {
                return v___x_2124_;
            }
            13 => {
                if v_isShared_2130_ == 0 {
                    v___x_2132_ = v___x_2129_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
                    v___x_2132_ = v_reuseFailAlloc_2133_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2132_;
            }
            15 => {
                if v_isShared_2145_ == 0 {
                    v___x_2147_ = v___x_2144_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2147_;
            }
            17 => {
                if v_isShared_2153_ == 0 {
                    v___x_2155_ = v___x_2152_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
                    v___x_2155_ = v_reuseFailAlloc_2156_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead___boxed(
    mut v_e_2158_: *mut leanh::LeanObject,
    mut v_a_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: *mut leanh::LeanObject,
    mut v_a_2161_: *mut leanh::LeanObject,
    mut v_a_2162_: *mut leanh::LeanObject,
    mut v_a_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
    mut v_a_2167_: *mut leanh::LeanObject,
    mut v_a_2168_: *mut leanh::LeanObject,
    mut v_a_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2170_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(
        v_e_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_,
        v_a_2166_, v_a_2167_, v_a_2168_,
    );
    leanh::lean_dec(v_a_2168_);
    leanh::lean_dec_ref(v_a_2167_);
    leanh::lean_dec(v_a_2166_);
    leanh::lean_dec_ref(v_a_2165_);
    leanh::lean_dec(v_a_2164_);
    leanh::lean_dec_ref(v_a_2163_);
    leanh::lean_dec(v_a_2162_);
    leanh::lean_dec_ref(v_a_2161_);
    leanh::lean_dec(v_a_2160_);
    leanh::lean_dec(v_a_2159_);
    return v_res_2170_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(
    mut v_cls_2171_: *mut leanh::LeanObject,
    mut v_msg_2172_: *mut leanh::LeanObject,
    mut v___y_2173_: *mut leanh::LeanObject,
    mut v___y_2174_: *mut leanh::LeanObject,
    mut v___y_2175_: *mut leanh::LeanObject,
    mut v___y_2176_: *mut leanh::LeanObject,
    mut v___y_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___redArg(v_cls_2171_, v_msg_2172_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
    return v___x_2184_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2___boxed(
    mut v_cls_2185_: *mut leanh::LeanObject,
    mut v_msg_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v___y_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
    mut v___y_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
    mut v___y_2194_: *mut leanh::LeanObject,
    mut v___y_2195_: *mut leanh::LeanObject,
    mut v___y_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead_spec__2(v_cls_2185_, v_msg_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
    leanh::lean_dec(v___y_2196_);
    leanh::lean_dec_ref(v___y_2195_);
    leanh::lean_dec(v___y_2194_);
    leanh::lean_dec_ref(v___y_2193_);
    leanh::lean_dec(v___y_2192_);
    leanh::lean_dec_ref(v___y_2191_);
    leanh::lean_dec(v___y_2190_);
    leanh::lean_dec_ref(v___y_2189_);
    leanh::lean_dec(v___y_2188_);
    leanh::lean_dec(v___y_2187_);
    return v_res_2198_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(
    mut v___x_2199_: u8,
    mut v_as_x27_2200_: *mut leanh::LeanObject,
    mut v_b_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
    mut v___y_2205_: *mut leanh::LeanObject,
    mut v___y_2206_: *mut leanh::LeanObject,
    mut v___y_2207_: *mut leanh::LeanObject,
    mut v___y_2208_: *mut leanh::LeanObject,
    mut v___y_2209_: *mut leanh::LeanObject,
    mut v___y_2210_: *mut leanh::LeanObject,
    mut v___y_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v_a_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2224_: u8 = 0;
    let mut v___x_2225_: u8 = 0;
    let mut v_fst_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryPostpone_2250_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2294_: u8 = 0;
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_fst_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2319_: u8 = 0;
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2200_) == 0 {
                    v___x_2213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2213_, 0, v_b_2201_);
                    return v___x_2213_;
                } else {
                    v_head_2214_ = leanh::lean_ctor_get(v_as_x27_2200_, 0);
                    v_tail_2215_ = leanh::lean_ctor_get(v_as_x27_2200_, 1);
                    v___x_2216_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_2202_);
                    if leanh::lean_obj_tag(v___x_2216_) == 0 {
                        v_snd_2217_ = leanh::lean_ctor_get(v_b_2201_, 1);
                        v_isSharedCheck_2314_ = (!leanh::lean_is_exclusive(v_b_2201_)) as u8;
                        if v_isSharedCheck_2314_ == 0 {
                            v_unused_2315_ = leanh::lean_ctor_get(v_b_2201_, 0);
                            leanh::lean_dec(v_unused_2315_);
                            v___x_2219_ = v_b_2201_;
                            v_isShared_2220_ = v_isSharedCheck_2314_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2217_);
                            leanh::lean_dec(v_b_2201_);
                            v___x_2219_ = leanh::lean_box(0);
                            v_isShared_2220_ = v_isSharedCheck_2314_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2201_);
                        v_a_2316_ = leanh::lean_ctor_get(v___x_2216_, 0);
                        v_isSharedCheck_2323_ =
                            (!leanh::lean_is_exclusive(v___x_2216_)) as u8;
                        if v_isSharedCheck_2323_ == 0 {
                            v___x_2318_ = v___x_2216_;
                            v_isShared_2319_ = v_isSharedCheck_2323_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2316_);
                            leanh::lean_dec(v___x_2216_);
                            v___x_2318_ = leanh::lean_box(0);
                            v_isShared_2319_ = v_isSharedCheck_2323_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_a_2221_ = leanh::lean_ctor_get(v___x_2216_, 0);
                v_isSharedCheck_2313_ = (!leanh::lean_is_exclusive(v___x_2216_)) as u8;
                if v_isSharedCheck_2313_ == 0 {
                    v___x_2223_ = v___x_2216_;
                    v_isShared_2224_ = v_isSharedCheck_2313_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2221_);
                    leanh::lean_dec(v___x_2216_);
                    v___x_2223_ = leanh::lean_box(0);
                    v_isShared_2224_ = v_isSharedCheck_2313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2225_ = (leanh::lean_unbox(v_a_2221_) as u8);
                leanh::lean_dec(v_a_2221_);
                if v___x_2225_ == 0 {
                    leanh::lean_del_object(v___x_2223_);
                    v_fst_2226_ = leanh::lean_ctor_get(v_snd_2217_, 0);
                    v_snd_2227_ = leanh::lean_ctor_get(v_snd_2217_, 1);
                    v_isSharedCheck_2295_ = (!leanh::lean_is_exclusive(v_snd_2217_)) as u8;
                    if v_isSharedCheck_2295_ == 0 {
                        v___x_2229_ = v_snd_2217_;
                        v_isShared_2230_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2227_);
                        leanh::lean_inc(v_fst_2226_);
                        leanh::lean_dec(v_snd_2217_);
                        v___x_2229_ = leanh::lean_box(0);
                        v_isShared_2230_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_fst_2296_ = leanh::lean_ctor_get(v_snd_2217_, 0);
                    v_snd_2297_ = leanh::lean_ctor_get(v_snd_2217_, 1);
                    v_isSharedCheck_2312_ = (!leanh::lean_is_exclusive(v_snd_2217_)) as u8;
                    if v_isSharedCheck_2312_ == 0 {
                        v___x_2299_ = v_snd_2217_;
                        v_isShared_2300_ = v_isSharedCheck_2312_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2297_);
                        leanh::lean_inc(v_fst_2296_);
                        leanh::lean_dec(v_snd_2217_);
                        v___x_2299_ = leanh::lean_box(0);
                        v_isShared_2300_ = v_isSharedCheck_2312_;
                        state = 18;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_head_2214_);
                v___x_2231_ = l_Lean_Meta_Grind_checkSplitStatus(
                    v_head_2214_,
                    v___y_2202_,
                    v___y_2203_,
                    v___y_2204_,
                    v___y_2205_,
                    v___y_2206_,
                    v___y_2207_,
                    v___y_2208_,
                    v___y_2209_,
                    v___y_2210_,
                    v___y_2211_,
                );
                if leanh::lean_obj_tag(v___x_2231_) == 0 {
                    v_a_2232_ = leanh::lean_ctor_get(v___x_2231_, 0);
                    leanh::lean_inc(v_a_2232_);
                    leanh::lean_dec_ref_known(v___x_2231_, 1);
                    v___x_2233_ = leanh::lean_box(0);
                    match leanh::lean_obj_tag(v_a_2232_) {
                        0 => {
                            leanh::lean_dec(v_snd_2227_);
                            v___x_2234_ = leanh::lean_box((v___x_2199_) as usize);
                            if v_isShared_2230_ == 0 {
                                leanh::lean_ctor_set(v___x_2229_, 1, v___x_2234_);
                                v___x_2236_ = v___x_2229_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2241_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_fst_2226_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2234_);
                                v___x_2236_ = v_reuseFailAlloc_2241_;
                                state = 4;
                                continue;
                            }
                        }
                        1 => {
                            leanh::lean_inc(v_head_2214_);
                            v___x_2242_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2242_, 0, v_head_2214_);
                            leanh::lean_ctor_set(v___x_2242_, 1, v_fst_2226_);
                            if v_isShared_2230_ == 0 {
                                leanh::lean_ctor_set(v___x_2229_, 0, v___x_2242_);
                                v___x_2244_ = v___x_2229_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2249_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2242_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_snd_2227_);
                                v___x_2244_ = v_reuseFailAlloc_2249_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            v_tryPostpone_2250_ = leanh::lean_ctor_get_uint8(
                                v_a_2232_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_a_2232_, 1);
                            if v_tryPostpone_2250_ == 0 {
                                v___x_2251_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2214_);
                                v___x_2252_ = l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_tryLookahead(v___x_2251_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
                                if leanh::lean_obj_tag(v___x_2252_) == 0 {
                                    v_a_2253_ = leanh::lean_ctor_get(v___x_2252_, 0);
                                    leanh::lean_inc(v_a_2253_);
                                    leanh::lean_dec_ref_known(v___x_2252_, 1);
                                    v___x_2254_ = (leanh::lean_unbox(v_a_2253_) as u8);
                                    leanh::lean_dec(v_a_2253_);
                                    if v___x_2254_ == 0 {
                                        leanh::lean_inc(v_head_2214_);
                                        v___x_2255_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2255_, 0, v_head_2214_);
                                        leanh::lean_ctor_set(v___x_2255_, 1, v_fst_2226_);
                                        if v_isShared_2230_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_2229_,
                                                0,
                                                v___x_2255_,
                                            );
                                            v___x_2257_ = v___x_2229_;
                                            state = 8;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2262_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2262_,
                                                0,
                                                v___x_2255_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2262_,
                                                1,
                                                v_snd_2227_,
                                            );
                                            v___x_2257_ = v_reuseFailAlloc_2262_;
                                            state = 8;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_snd_2227_);
                                        v___x_2263_ =
                                            leanh::lean_box((v___x_2199_) as usize);
                                        if v_isShared_2230_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_2229_,
                                                1,
                                                v___x_2263_,
                                            );
                                            v___x_2265_ = v___x_2229_;
                                            state = 10;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2270_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2270_,
                                                0,
                                                v_fst_2226_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2270_,
                                                1,
                                                v___x_2263_,
                                            );
                                            v___x_2265_ = v_reuseFailAlloc_2270_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_2229_);
                                    leanh::lean_dec(v_snd_2227_);
                                    leanh::lean_dec(v_fst_2226_);
                                    leanh::lean_del_object(v___x_2219_);
                                    v_a_2271_ = leanh::lean_ctor_get(v___x_2252_, 0);
                                    v_isSharedCheck_2278_ =
                                        (!leanh::lean_is_exclusive(v___x_2252_)) as u8;
                                    if v_isSharedCheck_2278_ == 0 {
                                        v___x_2273_ = v___x_2252_;
                                        v_isShared_2274_ = v_isSharedCheck_2278_;
                                        state = 12;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2271_);
                                        leanh::lean_dec(v___x_2252_);
                                        v___x_2273_ = leanh::lean_box(0);
                                        v_isShared_2274_ = v_isSharedCheck_2278_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_inc(v_head_2214_);
                                v___x_2279_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2279_, 0, v_head_2214_);
                                leanh::lean_ctor_set(v___x_2279_, 1, v_fst_2226_);
                                if v_isShared_2230_ == 0 {
                                    leanh::lean_ctor_set(v___x_2229_, 0, v___x_2279_);
                                    v___x_2281_ = v___x_2229_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2286_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2286_,
                                        0,
                                        v___x_2279_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2286_,
                                        1,
                                        v_snd_2227_,
                                    );
                                    v___x_2281_ = v_reuseFailAlloc_2286_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2229_);
                    leanh::lean_dec(v_snd_2227_);
                    leanh::lean_dec(v_fst_2226_);
                    leanh::lean_del_object(v___x_2219_);
                    v_a_2287_ = leanh::lean_ctor_get(v___x_2231_, 0);
                    v_isSharedCheck_2294_ = (!leanh::lean_is_exclusive(v___x_2231_)) as u8;
                    if v_isSharedCheck_2294_ == 0 {
                        v___x_2289_ = v___x_2231_;
                        v_isShared_2290_ = v_isSharedCheck_2294_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2287_);
                        leanh::lean_dec(v___x_2231_);
                        v___x_2289_ = leanh::lean_box(0);
                        v_isShared_2290_ = v_isSharedCheck_2294_;
                        state = 16;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2236_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2233_);
                    v___x_2238_ = v___x_2219_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_as_x27_2200_ = v_tail_2215_;
                v_b_2201_ = v___x_2238_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2244_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2233_);
                    v___x_2246_ = v___x_2219_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2244_);
                    v___x_2246_ = v_reuseFailAlloc_2248_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_as_x27_2200_ = v_tail_2215_;
                v_b_2201_ = v___x_2246_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2257_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2233_);
                    v___x_2259_ = v___x_2219_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 1, v___x_2257_);
                    v___x_2259_ = v_reuseFailAlloc_2261_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_as_x27_2200_ = v_tail_2215_;
                v_b_2201_ = v___x_2259_;
                state = 0;
                continue;
            }
            10 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2265_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2233_);
                    v___x_2267_ = v___x_2219_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 1, v___x_2265_);
                    v___x_2267_ = v_reuseFailAlloc_2269_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_as_x27_2200_ = v_tail_2215_;
                v_b_2201_ = v___x_2267_;
                state = 0;
                continue;
            }
            12 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2276_;
            }
            14 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2281_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2233_);
                    v___x_2283_ = v___x_2219_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2285_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2285_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_as_x27_2200_ = v_tail_2215_;
                v_b_2201_ = v___x_2283_;
                state = 0;
                continue;
            }
            16 => {
                if v_isShared_2290_ == 0 {
                    v___x_2292_ = v___x_2289_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
                    v___x_2292_ = v_reuseFailAlloc_2293_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2292_;
            }
            18 => {
                v___x_2301_ = leanh::lean_box((v___x_2199_) as usize);
                v___x_2302_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2302_, 0, v___x_2301_);
                if v_isShared_2300_ == 0 {
                    v___x_2304_ = v___x_2299_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_fst_2296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_snd_2297_);
                    v___x_2304_ = v_reuseFailAlloc_2311_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2304_);
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2302_);
                    v___x_2306_ = v___x_2219_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2310_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2304_);
                    v___x_2306_ = v_reuseFailAlloc_2310_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2224_ == 0 {
                    leanh::lean_ctor_set(v___x_2223_, 0, v___x_2306_);
                    v___x_2308_ = v___x_2223_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2308_;
            }
            22 => {
                if v_isShared_2319_ == 0 {
                    v___x_2321_ = v___x_2318_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
                    v___x_2321_ = v_reuseFailAlloc_2322_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg___boxed(
    mut v___x_2324_: *mut leanh::LeanObject,
    mut v_as_x27_2325_: *mut leanh::LeanObject,
    mut v_b_2326_: *mut leanh::LeanObject,
    mut v___y_2327_: *mut leanh::LeanObject,
    mut v___y_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_40167__boxed_2338_: u8 = 0;
    let mut v_res_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_40167__boxed_2338_ = (leanh::lean_unbox(v___x_2324_) as u8);
    v_res_2339_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(
        v___x_40167__boxed_2338_,
        v_as_x27_2325_,
        v_b_2326_,
        v___y_2327_,
        v___y_2328_,
        v___y_2329_,
        v___y_2330_,
        v___y_2331_,
        v___y_2332_,
        v___y_2333_,
        v___y_2334_,
        v___y_2335_,
        v___y_2336_,
    );
    leanh::lean_dec(v___y_2336_);
    leanh::lean_dec_ref(v___y_2335_);
    leanh::lean_dec(v___y_2334_);
    leanh::lean_dec_ref(v___y_2333_);
    leanh::lean_dec(v___y_2332_);
    leanh::lean_dec_ref(v___y_2331_);
    leanh::lean_dec(v___y_2330_);
    leanh::lean_dec_ref(v___y_2329_);
    leanh::lean_dec(v___y_2328_);
    leanh::lean_dec(v___y_2327_);
    leanh::lean_dec(v_as_x27_2325_);
    return v_res_2339_;
}
pub unsafe fn l_Lean_Meta_Grind_lookahead(
    mut v_a_2340_: *mut leanh::LeanObject,
    mut v_a_2341_: *mut leanh::LeanObject,
    mut v_a_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_a_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
    mut v_a_2348_: *mut leanh::LeanObject,
    mut v_a_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v_lookahead_2356_: u8 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v_split_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lookaheads_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v_nextDeclIdx_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_2385_: u8 = 0;
    let mut v_nextIdx_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v_num_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolved_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_argPosMap_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_argsAt_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2418_: u8 = 0;
    let mut v_split_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lookaheads_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v_fst_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v_nextDeclIdx_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_2456_: u8 = 0;
    let mut v_nextIdx_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v_num_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolved_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lookaheads_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_argPosMap_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_argsAt_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut v_isSharedCheck_2496_: u8 = 0;
    let mut v_unused_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut v_unused_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2504_: u8 = 0;
    let mut v_a_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2508_: u8 = 0;
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut v_reuseFailAlloc_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_unused_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v_unused_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v_unused_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2524_: u8 = 0;
    let mut v_unused_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_unused_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_a_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2351_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2342_);
                if leanh::lean_obj_tag(v___x_2351_) == 0 {
                    v_a_2352_ = leanh::lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2533_ = (!leanh::lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2533_ == 0 {
                        v___x_2354_ = v___x_2351_;
                        v_isShared_2355_ = v_isSharedCheck_2533_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2352_);
                        leanh::lean_dec(v___x_2351_);
                        v___x_2354_ = leanh::lean_box(0);
                        v_isShared_2355_ = v_isSharedCheck_2533_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2534_ = leanh::lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2541_ = (!leanh::lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2541_ == 0 {
                        v___x_2536_ = v___x_2351_;
                        v_isShared_2537_ = v_isSharedCheck_2541_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2534_);
                        leanh::lean_dec(v___x_2351_);
                        v___x_2536_ = leanh::lean_box(0);
                        v_isShared_2537_ = v_isSharedCheck_2541_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                v_lookahead_2356_ = leanh::lean_ctor_get_uint8(
                    v_a_2352_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 14) as u32,
                );
                leanh::lean_dec(v_a_2352_);
                if v_lookahead_2356_ == 0 {
                    v___x_2357_ = leanh::lean_box((v_lookahead_2356_) as usize);
                    if v_isShared_2355_ == 0 {
                        leanh::lean_ctor_set(v___x_2354_, 0, v___x_2357_);
                        v___x_2359_ = v___x_2354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
                        v___x_2359_ = v_reuseFailAlloc_2360_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2361_ = lean_st_ref_get(v_a_2340_);
                    v_toGoalState_2362_ = leanh::lean_ctor_get(v___x_2361_, 0);
                    v_isSharedCheck_2531_ = (!leanh::lean_is_exclusive(v___x_2361_)) as u8;
                    if v_isSharedCheck_2531_ == 0 {
                        v_unused_2532_ = leanh::lean_ctor_get(v___x_2361_, 1);
                        leanh::lean_dec(v_unused_2532_);
                        v___x_2364_ = v___x_2361_;
                        v_isShared_2365_ = v_isSharedCheck_2531_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_toGoalState_2362_);
                        leanh::lean_dec(v___x_2361_);
                        v___x_2364_ = leanh::lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2531_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2359_;
            }
            3 => {
                v_split_2366_ = leanh::lean_ctor_get(v_toGoalState_2362_, 14);
                leanh::lean_inc_ref(v_split_2366_);
                leanh::lean_dec_ref(v_toGoalState_2362_);
                v_lookaheads_2367_ = leanh::lean_ctor_get(v_split_2366_, 5);
                leanh::lean_inc(v_lookaheads_2367_);
                leanh::lean_dec_ref(v_split_2366_);
                v___x_2368_ = l_List_isEmpty___redArg(v_lookaheads_2367_);
                leanh::lean_dec(v_lookaheads_2367_);
                if v___x_2368_ == 0 {
                    leanh::lean_del_object(v___x_2354_);
                    v___x_2369_ = lean_st_ref_get(v_a_2340_);
                    v___x_2370_ = lean_st_ref_take(v_a_2340_);
                    v_toGoalState_2371_ = leanh::lean_ctor_get(v___x_2370_, 0);
                    leanh::lean_inc_ref(v_toGoalState_2371_);
                    v_split_2372_ = leanh::lean_ctor_get(v_toGoalState_2371_, 14);
                    leanh::lean_inc_ref(v_split_2372_);
                    v_mvarId_2373_ = leanh::lean_ctor_get(v___x_2370_, 1);
                    v_isSharedCheck_2524_ = (!leanh::lean_is_exclusive(v___x_2370_)) as u8;
                    if v_isSharedCheck_2524_ == 0 {
                        v_unused_2525_ = leanh::lean_ctor_get(v___x_2370_, 0);
                        leanh::lean_dec(v_unused_2525_);
                        v___x_2375_ = v___x_2370_;
                        v_isShared_2376_ = v_isSharedCheck_2524_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_mvarId_2373_);
                        leanh::lean_dec(v___x_2370_);
                        v___x_2375_ = leanh::lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2524_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2364_);
                    v___x_2526_ = 0;
                    v___x_2527_ = leanh::lean_box((v___x_2526_) as usize);
                    if v_isShared_2355_ == 0 {
                        leanh::lean_ctor_set(v___x_2354_, 0, v___x_2527_);
                        v___x_2529_ = v___x_2354_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
                        v___x_2529_ = v_reuseFailAlloc_2530_;
                        state = 25;
                        continue;
                    }
                }
            }
            4 => {
                v_nextDeclIdx_2377_ = leanh::lean_ctor_get(v_toGoalState_2371_, 0);
                v_enodeMap_2378_ = leanh::lean_ctor_get(v_toGoalState_2371_, 1);
                v_exprs_2379_ = leanh::lean_ctor_get(v_toGoalState_2371_, 2);
                v_parents_2380_ = leanh::lean_ctor_get(v_toGoalState_2371_, 3);
                v_congrTable_2381_ = leanh::lean_ctor_get(v_toGoalState_2371_, 4);
                v_appMap_2382_ = leanh::lean_ctor_get(v_toGoalState_2371_, 5);
                v_indicesFound_2383_ = leanh::lean_ctor_get(v_toGoalState_2371_, 6);
                v_newFacts_2384_ = leanh::lean_ctor_get(v_toGoalState_2371_, 7);
                v_inconsistent_2385_ = leanh::lean_ctor_get_uint8(
                    v_toGoalState_2371_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_2386_ = leanh::lean_ctor_get(v_toGoalState_2371_, 8);
                v_newRawFacts_2387_ = leanh::lean_ctor_get(v_toGoalState_2371_, 9);
                v_facts_2388_ = leanh::lean_ctor_get(v_toGoalState_2371_, 10);
                v_extThms_2389_ = leanh::lean_ctor_get(v_toGoalState_2371_, 11);
                v_ematch_2390_ = leanh::lean_ctor_get(v_toGoalState_2371_, 12);
                v_inj_2391_ = leanh::lean_ctor_get(v_toGoalState_2371_, 13);
                v_clean_2392_ = leanh::lean_ctor_get(v_toGoalState_2371_, 15);
                v_sstates_2393_ = leanh::lean_ctor_get(v_toGoalState_2371_, 16);
                v_isSharedCheck_2522_ =
                    (!leanh::lean_is_exclusive(v_toGoalState_2371_)) as u8;
                if v_isSharedCheck_2522_ == 0 {
                    v_unused_2523_ = leanh::lean_ctor_get(v_toGoalState_2371_, 14);
                    leanh::lean_dec(v_unused_2523_);
                    v___x_2395_ = v_toGoalState_2371_;
                    v_isShared_2396_ = v_isSharedCheck_2522_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_sstates_2393_);
                    leanh::lean_inc(v_clean_2392_);
                    leanh::lean_inc(v_inj_2391_);
                    leanh::lean_inc(v_ematch_2390_);
                    leanh::lean_inc(v_extThms_2389_);
                    leanh::lean_inc(v_facts_2388_);
                    leanh::lean_inc(v_newRawFacts_2387_);
                    leanh::lean_inc(v_nextIdx_2386_);
                    leanh::lean_inc(v_newFacts_2384_);
                    leanh::lean_inc(v_indicesFound_2383_);
                    leanh::lean_inc(v_appMap_2382_);
                    leanh::lean_inc(v_congrTable_2381_);
                    leanh::lean_inc(v_parents_2380_);
                    leanh::lean_inc(v_exprs_2379_);
                    leanh::lean_inc(v_enodeMap_2378_);
                    leanh::lean_inc(v_nextDeclIdx_2377_);
                    leanh::lean_dec(v_toGoalState_2371_);
                    v___x_2395_ = leanh::lean_box(0);
                    v_isShared_2396_ = v_isSharedCheck_2522_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_num_2397_ = leanh::lean_ctor_get(v_split_2372_, 0);
                v_candidates_2398_ = leanh::lean_ctor_get(v_split_2372_, 1);
                v_added_2399_ = leanh::lean_ctor_get(v_split_2372_, 2);
                v_resolved_2400_ = leanh::lean_ctor_get(v_split_2372_, 3);
                v_trace_2401_ = leanh::lean_ctor_get(v_split_2372_, 4);
                v_argPosMap_2402_ = leanh::lean_ctor_get(v_split_2372_, 6);
                v_argsAt_2403_ = leanh::lean_ctor_get(v_split_2372_, 7);
                v_isSharedCheck_2520_ = (!leanh::lean_is_exclusive(v_split_2372_)) as u8;
                if v_isSharedCheck_2520_ == 0 {
                    v_unused_2521_ = leanh::lean_ctor_get(v_split_2372_, 5);
                    leanh::lean_dec(v_unused_2521_);
                    v___x_2405_ = v_split_2372_;
                    v_isShared_2406_ = v_isSharedCheck_2520_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_argsAt_2403_);
                    leanh::lean_inc(v_argPosMap_2402_);
                    leanh::lean_inc(v_trace_2401_);
                    leanh::lean_inc(v_resolved_2400_);
                    leanh::lean_inc(v_added_2399_);
                    leanh::lean_inc(v_candidates_2398_);
                    leanh::lean_inc(v_num_2397_);
                    leanh::lean_dec(v_split_2372_);
                    v___x_2405_ = leanh::lean_box(0);
                    v_isShared_2406_ = v_isSharedCheck_2520_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2407_ = leanh::lean_box(0);
                if v_isShared_2406_ == 0 {
                    leanh::lean_ctor_set(v___x_2405_, 5, v___x_2407_);
                    v___x_2409_ = v___x_2405_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2519_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_num_2397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_candidates_2398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_added_2399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_resolved_2400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_trace_2401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 5, v___x_2407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 6, v_argPosMap_2402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 7, v_argsAt_2403_);
                    v___x_2409_ = v_reuseFailAlloc_2519_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2396_ == 0 {
                    leanh::lean_ctor_set(v___x_2395_, 14, v___x_2409_);
                    v___x_2411_ = v___x_2395_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_nextDeclIdx_2377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_enodeMap_2378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_exprs_2379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_parents_2380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_congrTable_2381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 5, v_appMap_2382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_indicesFound_2383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_newFacts_2384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_nextIdx_2386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 9, v_newRawFacts_2387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 10, v_facts_2388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 11, v_extThms_2389_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 12, v_ematch_2390_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 13, v_inj_2391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 14, v___x_2409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 15, v_clean_2392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 16, v_sstates_2393_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2518_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_2385_,
                    );
                    v___x_2411_ = v_reuseFailAlloc_2518_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2376_ == 0 {
                    leanh::lean_ctor_set(v___x_2375_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2375_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_mvarId_2373_);
                    v___x_2413_ = v_reuseFailAlloc_2517_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2414_ = lean_st_ref_set(v_a_2340_, v___x_2413_);
                v_toGoalState_2415_ = leanh::lean_ctor_get(v___x_2369_, 0);
                v_isSharedCheck_2515_ = (!leanh::lean_is_exclusive(v___x_2369_)) as u8;
                if v_isSharedCheck_2515_ == 0 {
                    v_unused_2516_ = leanh::lean_ctor_get(v___x_2369_, 1);
                    leanh::lean_dec(v_unused_2516_);
                    v___x_2417_ = v___x_2369_;
                    v_isShared_2418_ = v_isSharedCheck_2515_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_toGoalState_2415_);
                    leanh::lean_dec(v___x_2369_);
                    v___x_2417_ = leanh::lean_box(0);
                    v_isShared_2418_ = v_isSharedCheck_2515_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_split_2419_ = leanh::lean_ctor_get(v_toGoalState_2415_, 14);
                leanh::lean_inc_ref(v_split_2419_);
                leanh::lean_dec_ref(v_toGoalState_2415_);
                v_lookaheads_2420_ = leanh::lean_ctor_get(v_split_2419_, 5);
                leanh::lean_inc(v_lookaheads_2420_);
                leanh::lean_dec_ref(v_split_2419_);
                v___x_2421_ = leanh::lean_box(0);
                v___x_2422_ = leanh::lean_box((v___x_2368_) as usize);
                if v_isShared_2418_ == 0 {
                    leanh::lean_ctor_set(v___x_2417_, 1, v___x_2422_);
                    leanh::lean_ctor_set(v___x_2417_, 0, v___x_2407_);
                    v___x_2424_ = v___x_2417_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2422_);
                    v___x_2424_ = v_reuseFailAlloc_2514_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2365_ == 0 {
                    leanh::lean_ctor_set(v___x_2364_, 1, v___x_2424_);
                    leanh::lean_ctor_set(v___x_2364_, 0, v___x_2421_);
                    v___x_2426_ = v___x_2364_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2513_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2513_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2427_ =
                    l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(
                        v_lookahead_2356_,
                        v_lookaheads_2420_,
                        v___x_2426_,
                        v_a_2340_,
                        v_a_2341_,
                        v_a_2342_,
                        v_a_2343_,
                        v_a_2344_,
                        v_a_2345_,
                        v_a_2346_,
                        v_a_2347_,
                        v_a_2348_,
                        v_a_2349_,
                    );
                leanh::lean_dec(v_lookaheads_2420_);
                if leanh::lean_obj_tag(v___x_2427_) == 0 {
                    v_a_2428_ = leanh::lean_ctor_get(v___x_2427_, 0);
                    v_isSharedCheck_2504_ = (!leanh::lean_is_exclusive(v___x_2427_)) as u8;
                    if v_isSharedCheck_2504_ == 0 {
                        v___x_2430_ = v___x_2427_;
                        v_isShared_2431_ = v_isSharedCheck_2504_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2428_);
                        leanh::lean_dec(v___x_2427_);
                        v___x_2430_ = leanh::lean_box(0);
                        v_isShared_2431_ = v_isSharedCheck_2504_;
                        state = 13;
                        continue;
                    }
                } else {
                    v_a_2505_ = leanh::lean_ctor_get(v___x_2427_, 0);
                    v_isSharedCheck_2512_ = (!leanh::lean_is_exclusive(v___x_2427_)) as u8;
                    if v_isSharedCheck_2512_ == 0 {
                        v___x_2507_ = v___x_2427_;
                        v_isShared_2508_ = v_isSharedCheck_2512_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2505_);
                        leanh::lean_dec(v___x_2427_);
                        v___x_2507_ = leanh::lean_box(0);
                        v_isShared_2508_ = v_isSharedCheck_2512_;
                        state = 23;
                        continue;
                    }
                }
            }
            13 => {
                v_fst_2432_ = leanh::lean_ctor_get(v_a_2428_, 0);
                if leanh::lean_obj_tag(v_fst_2432_) == 0 {
                    v_snd_2433_ = leanh::lean_ctor_get(v_a_2428_, 1);
                    leanh::lean_inc(v_snd_2433_);
                    leanh::lean_dec(v_a_2428_);
                    v_snd_2434_ = leanh::lean_ctor_get(v_snd_2433_, 1);
                    v___x_2435_ = (leanh::lean_unbox(v_snd_2434_) as u8);
                    if v___x_2435_ == 0 {
                        leanh::lean_dec(v_snd_2433_);
                        v___x_2436_ = leanh::lean_box((v___x_2368_) as usize);
                        if v_isShared_2431_ == 0 {
                            leanh::lean_ctor_set(v___x_2430_, 0, v___x_2436_);
                            v___x_2438_ = v___x_2430_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2439_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
                            v___x_2438_ = v_reuseFailAlloc_2439_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v_fst_2440_ = leanh::lean_ctor_get(v_snd_2433_, 0);
                        leanh::lean_inc(v_fst_2440_);
                        leanh::lean_dec(v_snd_2433_);
                        v___x_2441_ = lean_st_ref_take(v_a_2340_);
                        v_toGoalState_2442_ = leanh::lean_ctor_get(v___x_2441_, 0);
                        leanh::lean_inc_ref(v_toGoalState_2442_);
                        v_split_2443_ = leanh::lean_ctor_get(v_toGoalState_2442_, 14);
                        leanh::lean_inc_ref(v_split_2443_);
                        v_mvarId_2444_ = leanh::lean_ctor_get(v___x_2441_, 1);
                        v_isSharedCheck_2498_ =
                            (!leanh::lean_is_exclusive(v___x_2441_)) as u8;
                        if v_isSharedCheck_2498_ == 0 {
                            v_unused_2499_ = leanh::lean_ctor_get(v___x_2441_, 0);
                            leanh::lean_dec(v_unused_2499_);
                            v___x_2446_ = v___x_2441_;
                            v_isShared_2447_ = v_isSharedCheck_2498_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_mvarId_2444_);
                            leanh::lean_dec(v___x_2441_);
                            v___x_2446_ = leanh::lean_box(0);
                            v_isShared_2447_ = v_isSharedCheck_2498_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2432_);
                    leanh::lean_dec(v_a_2428_);
                    v_val_2500_ = leanh::lean_ctor_get(v_fst_2432_, 0);
                    leanh::lean_inc(v_val_2500_);
                    leanh::lean_dec_ref_known(v_fst_2432_, 1);
                    if v_isShared_2431_ == 0 {
                        leanh::lean_ctor_set(v___x_2430_, 0, v_val_2500_);
                        v___x_2502_ = v___x_2430_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2503_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_val_2500_);
                        v___x_2502_ = v_reuseFailAlloc_2503_;
                        state = 22;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_2438_;
            }
            15 => {
                v_nextDeclIdx_2448_ = leanh::lean_ctor_get(v_toGoalState_2442_, 0);
                v_enodeMap_2449_ = leanh::lean_ctor_get(v_toGoalState_2442_, 1);
                v_exprs_2450_ = leanh::lean_ctor_get(v_toGoalState_2442_, 2);
                v_parents_2451_ = leanh::lean_ctor_get(v_toGoalState_2442_, 3);
                v_congrTable_2452_ = leanh::lean_ctor_get(v_toGoalState_2442_, 4);
                v_appMap_2453_ = leanh::lean_ctor_get(v_toGoalState_2442_, 5);
                v_indicesFound_2454_ = leanh::lean_ctor_get(v_toGoalState_2442_, 6);
                v_newFacts_2455_ = leanh::lean_ctor_get(v_toGoalState_2442_, 7);
                v_inconsistent_2456_ = leanh::lean_ctor_get_uint8(
                    v_toGoalState_2442_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_2457_ = leanh::lean_ctor_get(v_toGoalState_2442_, 8);
                v_newRawFacts_2458_ = leanh::lean_ctor_get(v_toGoalState_2442_, 9);
                v_facts_2459_ = leanh::lean_ctor_get(v_toGoalState_2442_, 10);
                v_extThms_2460_ = leanh::lean_ctor_get(v_toGoalState_2442_, 11);
                v_ematch_2461_ = leanh::lean_ctor_get(v_toGoalState_2442_, 12);
                v_inj_2462_ = leanh::lean_ctor_get(v_toGoalState_2442_, 13);
                v_clean_2463_ = leanh::lean_ctor_get(v_toGoalState_2442_, 15);
                v_sstates_2464_ = leanh::lean_ctor_get(v_toGoalState_2442_, 16);
                v_isSharedCheck_2496_ =
                    (!leanh::lean_is_exclusive(v_toGoalState_2442_)) as u8;
                if v_isSharedCheck_2496_ == 0 {
                    v_unused_2497_ = leanh::lean_ctor_get(v_toGoalState_2442_, 14);
                    leanh::lean_dec(v_unused_2497_);
                    v___x_2466_ = v_toGoalState_2442_;
                    v_isShared_2467_ = v_isSharedCheck_2496_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_inc(v_sstates_2464_);
                    leanh::lean_inc(v_clean_2463_);
                    leanh::lean_inc(v_inj_2462_);
                    leanh::lean_inc(v_ematch_2461_);
                    leanh::lean_inc(v_extThms_2460_);
                    leanh::lean_inc(v_facts_2459_);
                    leanh::lean_inc(v_newRawFacts_2458_);
                    leanh::lean_inc(v_nextIdx_2457_);
                    leanh::lean_inc(v_newFacts_2455_);
                    leanh::lean_inc(v_indicesFound_2454_);
                    leanh::lean_inc(v_appMap_2453_);
                    leanh::lean_inc(v_congrTable_2452_);
                    leanh::lean_inc(v_parents_2451_);
                    leanh::lean_inc(v_exprs_2450_);
                    leanh::lean_inc(v_enodeMap_2449_);
                    leanh::lean_inc(v_nextDeclIdx_2448_);
                    leanh::lean_dec(v_toGoalState_2442_);
                    v___x_2466_ = leanh::lean_box(0);
                    v_isShared_2467_ = v_isSharedCheck_2496_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_num_2468_ = leanh::lean_ctor_get(v_split_2443_, 0);
                v_candidates_2469_ = leanh::lean_ctor_get(v_split_2443_, 1);
                v_added_2470_ = leanh::lean_ctor_get(v_split_2443_, 2);
                v_resolved_2471_ = leanh::lean_ctor_get(v_split_2443_, 3);
                v_trace_2472_ = leanh::lean_ctor_get(v_split_2443_, 4);
                v_lookaheads_2473_ = leanh::lean_ctor_get(v_split_2443_, 5);
                v_argPosMap_2474_ = leanh::lean_ctor_get(v_split_2443_, 6);
                v_argsAt_2475_ = leanh::lean_ctor_get(v_split_2443_, 7);
                v_isSharedCheck_2495_ = (!leanh::lean_is_exclusive(v_split_2443_)) as u8;
                if v_isSharedCheck_2495_ == 0 {
                    v___x_2477_ = v_split_2443_;
                    v_isShared_2478_ = v_isSharedCheck_2495_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_argsAt_2475_);
                    leanh::lean_inc(v_argPosMap_2474_);
                    leanh::lean_inc(v_lookaheads_2473_);
                    leanh::lean_inc(v_trace_2472_);
                    leanh::lean_inc(v_resolved_2471_);
                    leanh::lean_inc(v_added_2470_);
                    leanh::lean_inc(v_candidates_2469_);
                    leanh::lean_inc(v_num_2468_);
                    leanh::lean_dec(v_split_2443_);
                    v___x_2477_ = leanh::lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2495_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2479_ = l_List_reverse___redArg(v_fst_2440_);
                v___x_2480_ = l_List_appendTR___redArg(v_lookaheads_2473_, v___x_2479_);
                if v_isShared_2478_ == 0 {
                    leanh::lean_ctor_set(v___x_2477_, 5, v___x_2480_);
                    v___x_2482_ = v___x_2477_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_num_2468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_candidates_2469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_added_2470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_resolved_2471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_trace_2472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 5, v___x_2480_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_argPosMap_2474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_argsAt_2475_);
                    v___x_2482_ = v_reuseFailAlloc_2494_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2467_ == 0 {
                    leanh::lean_ctor_set(v___x_2466_, 14, v___x_2482_);
                    v___x_2484_ = v___x_2466_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2493_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_nextDeclIdx_2448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_enodeMap_2449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_exprs_2450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_parents_2451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_congrTable_2452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_appMap_2453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_indicesFound_2454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_newFacts_2455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_nextIdx_2457_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 9, v_newRawFacts_2458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 10, v_facts_2459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 11, v_extThms_2460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 12, v_ematch_2461_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 13, v_inj_2462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 14, v___x_2482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 15, v_clean_2463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 16, v_sstates_2464_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2493_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_2456_,
                    );
                    v___x_2484_ = v_reuseFailAlloc_2493_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2447_ == 0 {
                    leanh::lean_ctor_set(v___x_2446_, 0, v___x_2484_);
                    v___x_2486_ = v___x_2446_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_mvarId_2444_);
                    v___x_2486_ = v_reuseFailAlloc_2492_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2487_ = lean_st_ref_set(v_a_2340_, v___x_2486_);
                v___x_2488_ = leanh::lean_box((v_lookahead_2356_) as usize);
                if v_isShared_2431_ == 0 {
                    leanh::lean_ctor_set(v___x_2430_, 0, v___x_2488_);
                    v___x_2490_ = v___x_2430_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
                    v___x_2490_ = v_reuseFailAlloc_2491_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2490_;
            }
            22 => {
                return v___x_2502_;
            }
            23 => {
                if v_isShared_2508_ == 0 {
                    v___x_2510_ = v___x_2507_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
                    v___x_2510_ = v_reuseFailAlloc_2511_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2510_;
            }
            25 => {
                return v___x_2529_;
            }
            26 => {
                if v_isShared_2537_ == 0 {
                    v___x_2539_ = v___x_2536_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_lookahead___boxed(
    mut v_a_2542_: *mut leanh::LeanObject,
    mut v_a_2543_: *mut leanh::LeanObject,
    mut v_a_2544_: *mut leanh::LeanObject,
    mut v_a_2545_: *mut leanh::LeanObject,
    mut v_a_2546_: *mut leanh::LeanObject,
    mut v_a_2547_: *mut leanh::LeanObject,
    mut v_a_2548_: *mut leanh::LeanObject,
    mut v_a_2549_: *mut leanh::LeanObject,
    mut v_a_2550_: *mut leanh::LeanObject,
    mut v_a_2551_: *mut leanh::LeanObject,
    mut v_a_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2553_ = l_Lean_Meta_Grind_lookahead(
        v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_,
        v_a_2550_, v_a_2551_,
    );
    leanh::lean_dec(v_a_2551_);
    leanh::lean_dec_ref(v_a_2550_);
    leanh::lean_dec(v_a_2549_);
    leanh::lean_dec_ref(v_a_2548_);
    leanh::lean_dec(v_a_2547_);
    leanh::lean_dec_ref(v_a_2546_);
    leanh::lean_dec(v_a_2545_);
    leanh::lean_dec_ref(v_a_2544_);
    leanh::lean_dec(v_a_2543_);
    leanh::lean_dec(v_a_2542_);
    return v_res_2553_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(
    mut v___x_2554_: u8,
    mut v_as_2555_: *mut leanh::LeanObject,
    mut v_as_x27_2556_: *mut leanh::LeanObject,
    mut v_b_2557_: *mut leanh::LeanObject,
    mut v_a_2558_: *mut leanh::LeanObject,
    mut v___y_2559_: *mut leanh::LeanObject,
    mut v___y_2560_: *mut leanh::LeanObject,
    mut v___y_2561_: *mut leanh::LeanObject,
    mut v___y_2562_: *mut leanh::LeanObject,
    mut v___y_2563_: *mut leanh::LeanObject,
    mut v___y_2564_: *mut leanh::LeanObject,
    mut v___y_2565_: *mut leanh::LeanObject,
    mut v___y_2566_: *mut leanh::LeanObject,
    mut v___y_2567_: *mut leanh::LeanObject,
    mut v___y_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___redArg(
        v___x_2554_,
        v_as_x27_2556_,
        v_b_2557_,
        v___y_2559_,
        v___y_2560_,
        v___y_2561_,
        v___y_2562_,
        v___y_2563_,
        v___y_2564_,
        v___y_2565_,
        v___y_2566_,
        v___y_2567_,
        v___y_2568_,
    );
    return v___x_2570_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0___boxed(
    mut v___x_2571_: *mut leanh::LeanObject,
    mut v_as_2572_: *mut leanh::LeanObject,
    mut v_as_x27_2573_: *mut leanh::LeanObject,
    mut v_b_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
    mut v___y_2576_: *mut leanh::LeanObject,
    mut v___y_2577_: *mut leanh::LeanObject,
    mut v___y_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
    mut v___y_2580_: *mut leanh::LeanObject,
    mut v___y_2581_: *mut leanh::LeanObject,
    mut v___y_2582_: *mut leanh::LeanObject,
    mut v___y_2583_: *mut leanh::LeanObject,
    mut v___y_2584_: *mut leanh::LeanObject,
    mut v___y_2585_: *mut leanh::LeanObject,
    mut v___y_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_40668__boxed_2587_: u8 = 0;
    let mut v_res_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_40668__boxed_2587_ = (leanh::lean_unbox(v___x_2571_) as u8);
    v_res_2588_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_lookahead_spec__0(
        v___x_40668__boxed_2587_,
        v_as_2572_,
        v_as_x27_2573_,
        v_b_2574_,
        v_a_2575_,
        v___y_2576_,
        v___y_2577_,
        v___y_2578_,
        v___y_2579_,
        v___y_2580_,
        v___y_2581_,
        v___y_2582_,
        v___y_2583_,
        v___y_2584_,
        v___y_2585_,
    );
    leanh::lean_dec(v___y_2585_);
    leanh::lean_dec_ref(v___y_2584_);
    leanh::lean_dec(v___y_2583_);
    leanh::lean_dec_ref(v___y_2582_);
    leanh::lean_dec(v___y_2581_);
    leanh::lean_dec_ref(v___y_2580_);
    leanh::lean_dec(v___y_2579_);
    leanh::lean_dec_ref(v___y_2578_);
    leanh::lean_dec(v___y_2577_);
    leanh::lean_dec(v___y_2576_);
    leanh::lean_dec(v_as_x27_2573_);
    leanh::lean_dec(v_as_2572_);
    return v_res_2588_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations =
        _init_l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Lookahead_0__Lean_Meta_Grind_maxIterations,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Lookahead(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Lookahead(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
}