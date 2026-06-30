// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpAll
// Imports: Lean.Meta.Tactic.Simp.Main
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_fset, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_uget_borrowed, lean_expr_eqv, lean_nat_add, lean_nat_dec_lt,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_num___override};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_hasMVar, l_Lean_Expr_isTrue,
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkExpectedTypeHint;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assertHypotheses;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClearMany;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_simpStep, l_Lean_Meta_simpTarget,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpTheoremsArray_addTheorem, l_Lean_Meta_SimpTheoremsArray_eraseTheorem,
    l_Lean_Meta_SimpTheoremsArray_isErased, l_Lean_Meta_instInhabitedOrigin_default,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Context_setSimpTheorems;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getNondepPropHyps, l_Lean_Meta_getPropHyps,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
pub static l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_SimpAll_instInhabitedEntry_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_SimpAll_instInhabitedEntry: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 147, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 4, m_data: [226, 134, 147, 32, 226, 134, 144, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 144, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3_value) as *mut leanh::LeanObject,3981491789317542566 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4_value) as *mut leanh::LeanObject,14676408778151084014 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 110, 116, 114, 121, 46, 105, 100, 58, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 61, 62, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_SimpAll_main___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_SimpAll_main___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SimpAll_main___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_simpAll___lam__0___closed__0_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            115, 105, 109, 112, 95, 97, 108, 108, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112,
            114, 111, 103, 114, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Meta_simpAll___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpAll___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_simpAll___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpAll___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_simpAll___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_simpAll___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpAll___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12926315994152569291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 105, 109, 112, 65, 108, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3211841996033938717 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,17642114082717827880 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1418255026943354753 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject,398904428817590593 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7289750419888819448 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8265095590626188105 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3025812853071538316 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject,5979030882983175600 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject,4236647998088007629 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,248106741383213221 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14394704767657729299 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 816399212 as usize) << 1) | 1) as *mut leanh::LeanObject,3641456706343106648 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12914754714115501343 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5504757222536137383 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,10400754432889756754 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = leanh::lean_box(0);
    v___x_1487_ = l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1;
    v___x_1488_ = l_Lean_Expr_const___override(v___x_1487_, v___x_1486_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2_once),
        _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2,
    );
    v___x_1490_ = l_Lean_Meta_instInhabitedOrigin_default;
    v___x_1491_ = leanh::lean_box(0);
    v___x_1492_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1492_, 0, v___x_1491_);
    leanh::lean_ctor_set(v___x_1492_, 1, v___x_1491_);
    leanh::lean_ctor_set(v___x_1492_, 2, v___x_1490_);
    leanh::lean_ctor_set(v___x_1492_, 3, v___x_1489_);
    leanh::lean_ctor_set(v___x_1492_, 4, v___x_1489_);
    leanh::lean_ctor_set(v___x_1492_, 5, v___x_1489_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default() -> *mut leanh::LeanObject
{
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3_once),
        _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3,
    );
    return v___x_1493_;
}
pub unsafe fn _init_l_Lean_Meta_SimpAll_instInhabitedEntry() -> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lean_Meta_SimpAll_instInhabitedEntry_default;
    return v___x_1494_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(
    mut v_x_1495_: *mut leanh::LeanObject,
    mut v___y_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1496_);
    v___x_1502_ = leanh::lean_apply_6(
        v_x_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
        v___y_1500_,
        leanh::lean_box(0),
    );
    return v___x_1502_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed(
    mut v_x_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
    mut v___y_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
    leanh::lean_dec(v___y_1504_);
    return v_res_1510_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(
    mut v_mvarId_1511_: *mut leanh::LeanObject,
    mut v_x_1512_: *mut leanh::LeanObject,
    mut v___y_1513_: *mut leanh::LeanObject,
    mut v___y_1514_: *mut leanh::LeanObject,
    mut v___y_1515_: *mut leanh::LeanObject,
    mut v___y_1516_: *mut leanh::LeanObject,
    mut v___y_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1513_);
                v___f_1519_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                leanh::lean_closure_set(v___f_1519_, 0, v_x_1512_);
                leanh::lean_closure_set(v___f_1519_, 1, v___y_1513_);
                v___x_1520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1511_,
                    v___f_1519_,
                    v___y_1514_,
                    v___y_1515_,
                    v___y_1516_,
                    v___y_1517_,
                );
                if leanh::lean_obj_tag(v___x_1520_) == 0 {
                    return v___x_1520_;
                } else {
                    v_a_1521_ = leanh::lean_ctor_get(v___x_1520_, 0);
                    v_isSharedCheck_1528_ = (!leanh::lean_is_exclusive(v___x_1520_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1523_ = v___x_1520_;
                        v_isShared_1524_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1521_);
                        leanh::lean_dec(v___x_1520_);
                        v___x_1523_ = leanh::lean_box(0);
                        v_isShared_1524_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1524_ == 0 {
                    v___x_1526_ = v___x_1523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___boxed(
    mut v_mvarId_1529_: *mut leanh::LeanObject,
    mut v_x_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_1529_, v_x_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
    leanh::lean_dec(v___y_1535_);
    leanh::lean_dec_ref(v___y_1534_);
    leanh::lean_dec(v___y_1533_);
    leanh::lean_dec_ref(v___y_1532_);
    leanh::lean_dec(v___y_1531_);
    return v_res_1537_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(
    mut v_00_u03b1_1538_: *mut leanh::LeanObject,
    mut v_mvarId_1539_: *mut leanh::LeanObject,
    mut v_x_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
    mut v___y_1543_: *mut leanh::LeanObject,
    mut v___y_1544_: *mut leanh::LeanObject,
    mut v___y_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_1539_, v_x_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
    return v___x_1547_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___boxed(
    mut v_00_u03b1_1548_: *mut leanh::LeanObject,
    mut v_mvarId_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
    mut v___y_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(v_00_u03b1_1548_, v_mvarId_1549_, v_x_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
    leanh::lean_dec(v___y_1555_);
    leanh::lean_dec_ref(v___y_1554_);
    leanh::lean_dec(v___y_1553_);
    leanh::lean_dec_ref(v___y_1552_);
    leanh::lean_dec(v___y_1551_);
    return v_res_1557_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(
    mut v_e_1558_: *mut leanh::LeanObject,
    mut v___y_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_unused_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1561_ = l_Lean_Expr_hasMVar(v_e_1558_);
                if v___x_1561_ == 0 {
                    v___x_1562_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1562_, 0, v_e_1558_);
                    return v___x_1562_;
                } else {
                    v___x_1563_ = lean_st_ref_get(v___y_1559_);
                    v_mctx_1564_ = leanh::lean_ctor_get(v___x_1563_, 0);
                    leanh::lean_inc_ref(v_mctx_1564_);
                    leanh::lean_dec(v___x_1563_);
                    v___x_1565_ = l_Lean_instantiateMVarsCore(v_mctx_1564_, v_e_1558_);
                    v_fst_1566_ = leanh::lean_ctor_get(v___x_1565_, 0);
                    leanh::lean_inc(v_fst_1566_);
                    v_snd_1567_ = leanh::lean_ctor_get(v___x_1565_, 1);
                    leanh::lean_inc(v_snd_1567_);
                    leanh::lean_dec_ref(v___x_1565_);
                    v___x_1568_ = lean_st_ref_take(v___y_1559_);
                    v_cache_1569_ = leanh::lean_ctor_get(v___x_1568_, 1);
                    v_zetaDeltaFVarIds_1570_ = leanh::lean_ctor_get(v___x_1568_, 2);
                    v_postponed_1571_ = leanh::lean_ctor_get(v___x_1568_, 3);
                    v_diag_1572_ = leanh::lean_ctor_get(v___x_1568_, 4);
                    v_isSharedCheck_1581_ = (!leanh::lean_is_exclusive(v___x_1568_)) as u8;
                    if v_isSharedCheck_1581_ == 0 {
                        v_unused_1582_ = leanh::lean_ctor_get(v___x_1568_, 0);
                        leanh::lean_dec(v_unused_1582_);
                        v___x_1574_ = v___x_1568_;
                        v_isShared_1575_ = v_isSharedCheck_1581_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1572_);
                        leanh::lean_inc(v_postponed_1571_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1570_);
                        leanh::lean_inc(v_cache_1569_);
                        leanh::lean_dec(v___x_1568_);
                        v___x_1574_ = leanh::lean_box(0);
                        v_isShared_1575_ = v_isSharedCheck_1581_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1575_ == 0 {
                    leanh::lean_ctor_set(v___x_1574_, 0, v_snd_1567_);
                    v___x_1577_ = v___x_1574_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_snd_1567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_cache_1569_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1580_,
                        2,
                        v_zetaDeltaFVarIds_1570_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_postponed_1571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_diag_1572_);
                    v___x_1577_ = v_reuseFailAlloc_1580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1578_ = lean_st_ref_set(v___y_1559_, v___x_1577_);
                v___x_1579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1579_, 0, v_fst_1566_);
                return v___x_1579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg___boxed(
    mut v_e_1583_: *mut leanh::LeanObject,
    mut v___y_1584_: *mut leanh::LeanObject,
    mut v___y_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_1583_, v___y_1584_);
    leanh::lean_dec(v___y_1584_);
    return v_res_1586_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(
    mut v_e_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
    mut v___y_1591_: *mut leanh::LeanObject,
    mut v___y_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_1587_, v___y_1590_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___boxed(
    mut v_e_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(v_e_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
    leanh::lean_dec(v___y_1600_);
    leanh::lean_dec_ref(v___y_1599_);
    leanh::lean_dec(v___y_1598_);
    leanh::lean_dec_ref(v___y_1597_);
    leanh::lean_dec(v___y_1596_);
    return v_res_1602_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
    mut v___y_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_Meta_getPropHyps(v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
    return v___x_1609_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed(
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1616_ =
        l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(
            v___y_1610_,
            v___y_1611_,
            v___y_1612_,
            v___y_1613_,
            v___y_1614_,
        );
    leanh::lean_dec(v___y_1614_);
    leanh::lean_dec_ref(v___y_1613_);
    leanh::lean_dec(v___y_1612_);
    leanh::lean_dec_ref(v___y_1611_);
    leanh::lean_dec(v___y_1610_);
    return v_res_1616_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(
    mut v_a_1617_: *mut leanh::LeanObject,
    mut v_as_1618_: *mut leanh::LeanObject,
    mut v_i_1619_: usize,
    mut v_stop_1620_: usize,
) -> u8 {
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: usize = 0;
    let mut v___x_1625_: usize = 0;
    let mut v___x_1627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1621_ = lean_usize_dec_eq(v_i_1619_, v_stop_1620_);
                if v___x_1621_ == 0 {
                    v___x_1622_ = lean_array_uget_borrowed(v_as_1618_, v_i_1619_);
                    v___x_1623_ = l_Lean_instBEqFVarId_beq(v_a_1617_, v___x_1622_);
                    if v___x_1623_ == 0 {
                        v___x_1624_ = 1usize;
                        v___x_1625_ = lean_usize_add(v_i_1619_, v___x_1624_);
                        v_i_1619_ = v___x_1625_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1623_;
                    }
                } else {
                    v___x_1627_ = 0;
                    return v___x_1627_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1___boxed(
    mut v_a_1628_: *mut leanh::LeanObject,
    mut v_as_1629_: *mut leanh::LeanObject,
    mut v_i_1630_: *mut leanh::LeanObject,
    mut v_stop_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1632_: usize = 0;
    let mut v_stop_boxed_1633_: usize = 0;
    let mut v_res_1634_: u8 = 0;
    let mut v_r_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1632_ = leanh::lean_unbox_usize(v_i_1630_);
    leanh::lean_dec(v_i_1630_);
    v_stop_boxed_1633_ = leanh::lean_unbox_usize(v_stop_1631_);
    leanh::lean_dec(v_stop_1631_);
    v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_1628_, v_as_1629_, v_i_boxed_1632_, v_stop_boxed_1633_);
    leanh::lean_dec_ref(v_as_1629_);
    leanh::lean_dec(v_a_1628_);
    v_r_1635_ = leanh::lean_box((v_res_1634_) as usize);
    return v_r_1635_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(
    mut v_as_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    v___x_1638_ = leanh::lean_unsigned_to_nat(0);
    v___x_1639_ = lean_array_get_size(v_as_1636_);
    v___x_1640_ = lean_nat_dec_lt(v___x_1638_, v___x_1639_);
    if v___x_1640_ == 0 {
        return v___x_1640_;
    } else {
        if v___x_1640_ == 0 {
            return v___x_1640_;
        } else {
            let mut v___x_1641_: usize = 0;
            let mut v___x_1642_: usize = 0;
            let mut v___x_1643_: u8 = 0;
            v___x_1641_ = 0usize;
            v___x_1642_ = lean_usize_of_nat(v___x_1639_);
            v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_1637_, v_as_1636_, v___x_1641_, v___x_1642_);
            return v___x_1643_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1___boxed(
    mut v_as_1644_: *mut leanh::LeanObject,
    mut v_a_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_as_1644_, v_a_1645_);
    leanh::lean_dec(v_a_1645_);
    leanh::lean_dec_ref(v_as_1644_);
    v_r_1647_ = leanh::lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v_as_1649_: *mut leanh::LeanObject,
    mut v_sz_1650_: usize,
    mut v_i_1651_: usize,
    mut v_b_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: usize = 0;
    let mut v___x_1662_: usize = 0;
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexConfig_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_1678_: u8 = 0;
    let mut v_mvarId_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_1699_: u8 = 0;
    let mut v_mvarId_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v_a_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v_reuseFailAlloc_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut v_a_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1664_ = lean_usize_dec_lt(v_i_1651_, v_sz_1650_);
                if v___x_1664_ == 0 {
                    v___x_1665_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1665_, 0, v_b_1652_);
                    return v___x_1665_;
                } else {
                    v_a_1666_ = lean_array_uget_borrowed(v_as_1649_, v_i_1651_);
                    leanh::lean_inc(v_a_1666_);
                    v___x_1667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1667_, 0, v_a_1666_);
                    v___x_1668_ = l_Lean_Meta_SimpTheoremsArray_isErased(v_b_1652_, v___x_1667_);
                    if v___x_1668_ == 0 {
                        leanh::lean_inc(v_a_1666_);
                        v___x_1669_ = l_Lean_FVarId_getDecl___redArg(
                            v_a_1666_,
                            v___y_1654_,
                            v___y_1656_,
                            v___y_1657_,
                        );
                        if leanh::lean_obj_tag(v___x_1669_) == 0 {
                            v_a_1670_ = leanh::lean_ctor_get(v___x_1669_, 0);
                            leanh::lean_inc_n(v_a_1670_, 2);
                            leanh::lean_dec_ref_known(v___x_1669_, 1);
                            v___x_1671_ = lean_st_ref_get(v___y_1653_);
                            v_ctx_1672_ = leanh::lean_ctor_get(v___x_1671_, 2);
                            leanh::lean_inc_ref(v_ctx_1672_);
                            leanh::lean_dec(v___x_1671_);
                            v_indexConfig_1673_ = leanh::lean_ctor_get(v_ctx_1672_, 5);
                            leanh::lean_inc_ref(v_indexConfig_1673_);
                            leanh::lean_dec_ref(v_ctx_1672_);
                            v___x_1674_ = l_Lean_LocalDecl_toExpr(v_a_1670_);
                            leanh::lean_inc_ref(v___x_1674_);
                            leanh::lean_inc_ref(v___x_1667_);
                            v___x_1675_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                                v_b_1652_,
                                v___x_1667_,
                                v___x_1674_,
                                v_indexConfig_1673_,
                                v___y_1654_,
                                v___y_1655_,
                                v___y_1656_,
                                v___y_1657_,
                            );
                            if leanh::lean_obj_tag(v___x_1675_) == 0 {
                                v_a_1676_ = leanh::lean_ctor_get(v___x_1675_, 0);
                                leanh::lean_inc(v_a_1676_);
                                leanh::lean_dec_ref_known(v___x_1675_, 1);
                                v___x_1677_ = lean_st_ref_take(v___y_1653_);
                                v_modified_1678_ = leanh::lean_ctor_get_uint8(
                                    v___x_1677_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6)
                                        as u32,
                                );
                                v_mvarId_1679_ = leanh::lean_ctor_get(v___x_1677_, 0);
                                v_entries_1680_ = leanh::lean_ctor_get(v___x_1677_, 1);
                                v_ctx_1681_ = leanh::lean_ctor_get(v___x_1677_, 2);
                                v_simprocs_1682_ = leanh::lean_ctor_get(v___x_1677_, 3);
                                v_usedTheorems_1683_ = leanh::lean_ctor_get(v___x_1677_, 4);
                                v_diag_1684_ = leanh::lean_ctor_get(v___x_1677_, 5);
                                v_isSharedCheck_1724_ =
                                    (!leanh::lean_is_exclusive(v___x_1677_)) as u8;
                                if v_isSharedCheck_1724_ == 0 {
                                    v___x_1686_ = v___x_1677_;
                                    v_isShared_1687_ = v_isSharedCheck_1724_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_diag_1684_);
                                    leanh::lean_inc(v_usedTheorems_1683_);
                                    leanh::lean_inc(v_simprocs_1682_);
                                    leanh::lean_inc(v_ctx_1681_);
                                    leanh::lean_inc(v_entries_1680_);
                                    leanh::lean_inc(v_mvarId_1679_);
                                    leanh::lean_dec(v___x_1677_);
                                    v___x_1686_ = leanh::lean_box(0);
                                    v_isShared_1687_ = v_isSharedCheck_1724_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1674_);
                                leanh::lean_dec(v_a_1670_);
                                leanh::lean_dec_ref_known(v___x_1667_, 1);
                                return v___x_1675_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_1667_, 1);
                            leanh::lean_dec_ref(v_b_1652_);
                            v_a_1725_ = leanh::lean_ctor_get(v___x_1669_, 0);
                            v_isSharedCheck_1732_ =
                                (!leanh::lean_is_exclusive(v___x_1669_)) as u8;
                            if v_isSharedCheck_1732_ == 0 {
                                v___x_1727_ = v___x_1669_;
                                v_isShared_1728_ = v_isSharedCheck_1732_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1725_);
                                leanh::lean_dec(v___x_1669_);
                                v___x_1727_ = leanh::lean_box(0);
                                v_isShared_1728_ = v_isSharedCheck_1732_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_1667_, 1);
                        v_a_1660_ = v_b_1652_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1661_ = 1usize;
                v___x_1662_ = lean_usize_add(v_i_1651_, v___x_1661_);
                v_i_1651_ = v___x_1662_;
                v_b_1652_ = v_a_1660_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v_a_1676_);
                v___x_1688_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_1681_, v_a_1676_);
                if v_isShared_1687_ == 0 {
                    leanh::lean_ctor_set(v___x_1686_, 2, v___x_1688_);
                    v___x_1690_ = v___x_1686_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_mvarId_1679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_entries_1680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 2, v___x_1688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_simprocs_1682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_usedTheorems_1683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_diag_1684_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1723_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_modified_1678_,
                    );
                    v___x_1690_ = v_reuseFailAlloc_1723_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1691_ = lean_st_ref_set(v___y_1653_, v___x_1690_);
                v___x_1692_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_a_1648_, v_a_1666_);
                if v___x_1692_ == 0 {
                    leanh::lean_dec_ref(v___x_1674_);
                    leanh::lean_dec(v_a_1670_);
                    leanh::lean_dec_ref_known(v___x_1667_, 1);
                    v_a_1660_ = v_a_1676_;
                    state = 1;
                    continue;
                } else {
                    v___x_1693_ = l_Lean_LocalDecl_type(v_a_1670_);
                    v___x_1694_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v___x_1693_, v___y_1655_);
                    if leanh::lean_obj_tag(v___x_1694_) == 0 {
                        v_a_1695_ = leanh::lean_ctor_get(v___x_1694_, 0);
                        leanh::lean_inc_n(v_a_1695_, 2);
                        leanh::lean_dec_ref_known(v___x_1694_, 1);
                        v___x_1696_ = l_Lean_LocalDecl_userName(v_a_1670_);
                        leanh::lean_dec(v_a_1670_);
                        leanh::lean_inc(v_a_1666_);
                        v___x_1697_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        leanh::lean_ctor_set(v___x_1697_, 0, v_a_1666_);
                        leanh::lean_ctor_set(v___x_1697_, 1, v___x_1696_);
                        leanh::lean_ctor_set(v___x_1697_, 2, v___x_1667_);
                        leanh::lean_ctor_set(v___x_1697_, 3, v_a_1695_);
                        leanh::lean_ctor_set(v___x_1697_, 4, v_a_1695_);
                        leanh::lean_ctor_set(v___x_1697_, 5, v___x_1674_);
                        v___x_1698_ = lean_st_ref_take(v___y_1653_);
                        v_modified_1699_ = leanh::lean_ctor_get_uint8(
                            v___x_1698_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        );
                        v_mvarId_1700_ = leanh::lean_ctor_get(v___x_1698_, 0);
                        v_entries_1701_ = leanh::lean_ctor_get(v___x_1698_, 1);
                        v_ctx_1702_ = leanh::lean_ctor_get(v___x_1698_, 2);
                        v_simprocs_1703_ = leanh::lean_ctor_get(v___x_1698_, 3);
                        v_usedTheorems_1704_ = leanh::lean_ctor_get(v___x_1698_, 4);
                        v_diag_1705_ = leanh::lean_ctor_get(v___x_1698_, 5);
                        v_isSharedCheck_1714_ =
                            (!leanh::lean_is_exclusive(v___x_1698_)) as u8;
                        if v_isSharedCheck_1714_ == 0 {
                            v___x_1707_ = v___x_1698_;
                            v_isShared_1708_ = v_isSharedCheck_1714_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_diag_1705_);
                            leanh::lean_inc(v_usedTheorems_1704_);
                            leanh::lean_inc(v_simprocs_1703_);
                            leanh::lean_inc(v_ctx_1702_);
                            leanh::lean_inc(v_entries_1701_);
                            leanh::lean_inc(v_mvarId_1700_);
                            leanh::lean_dec(v___x_1698_);
                            v___x_1707_ = leanh::lean_box(0);
                            v_isShared_1708_ = v_isSharedCheck_1714_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1676_);
                        leanh::lean_dec_ref(v___x_1674_);
                        leanh::lean_dec(v_a_1670_);
                        leanh::lean_dec_ref_known(v___x_1667_, 1);
                        v_a_1715_ = leanh::lean_ctor_get(v___x_1694_, 0);
                        v_isSharedCheck_1722_ =
                            (!leanh::lean_is_exclusive(v___x_1694_)) as u8;
                        if v_isSharedCheck_1722_ == 0 {
                            v___x_1717_ = v___x_1694_;
                            v_isShared_1718_ = v_isSharedCheck_1722_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1715_);
                            leanh::lean_dec(v___x_1694_);
                            v___x_1717_ = leanh::lean_box(0);
                            v_isShared_1718_ = v_isSharedCheck_1722_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1709_ = lean_array_push(v_entries_1701_, v___x_1697_);
                if v_isShared_1708_ == 0 {
                    leanh::lean_ctor_set(v___x_1707_, 1, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_mvarId_1700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_ctx_1702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_simprocs_1703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_usedTheorems_1704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 5, v_diag_1705_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1713_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_modified_1699_,
                    );
                    v___x_1711_ = v_reuseFailAlloc_1713_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1712_ = lean_st_ref_set(v___y_1653_, v___x_1711_);
                v_a_1660_ = v_a_1676_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_1718_ == 0 {
                    v___x_1720_ = v___x_1717_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
                    v___x_1720_ = v_reuseFailAlloc_1721_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1720_;
            }
            8 => {
                if v_isShared_1728_ == 0 {
                    v___x_1730_ = v___x_1727_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3___boxed(
    mut v_a_1733_: *mut leanh::LeanObject,
    mut v_as_1734_: *mut leanh::LeanObject,
    mut v_sz_1735_: *mut leanh::LeanObject,
    mut v_i_1736_: *mut leanh::LeanObject,
    mut v_b_1737_: *mut leanh::LeanObject,
    mut v___y_1738_: *mut leanh::LeanObject,
    mut v___y_1739_: *mut leanh::LeanObject,
    mut v___y_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1744_: usize = 0;
    let mut v_i_boxed_1745_: usize = 0;
    let mut v_res_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1744_ = leanh::lean_unbox_usize(v_sz_1735_);
    leanh::lean_dec(v_sz_1735_);
    v_i_boxed_1745_ = leanh::lean_unbox_usize(v_i_1736_);
    leanh::lean_dec(v_i_1736_);
    v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_1733_, v_as_1734_, v_sz_boxed_1744_, v_i_boxed_1745_, v_b_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
    leanh::lean_dec(v___y_1742_);
    leanh::lean_dec_ref(v___y_1741_);
    leanh::lean_dec(v___y_1740_);
    leanh::lean_dec_ref(v___y_1739_);
    leanh::lean_dec(v___y_1738_);
    leanh::lean_dec_ref(v_as_1734_);
    leanh::lean_dec_ref(v_a_1733_);
    return v_res_1746_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(
    mut v_a_1748_: *mut leanh::LeanObject,
    mut v_a_1749_: *mut leanh::LeanObject,
    mut v_a_1750_: *mut leanh::LeanObject,
    mut v_a_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpTheorems_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1766_: usize = 0;
    let mut v___x_1767_: usize = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_unused_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_a_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_a_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1754_ = lean_st_ref_get(v_a_1748_);
                v_mvarId_1755_ = leanh::lean_ctor_get(v___x_1754_, 0);
                leanh::lean_inc(v_mvarId_1755_);
                leanh::lean_dec(v___x_1754_);
                v___f_1756_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0;
                v___x_1757_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_1755_, v___f_1756_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
                if leanh::lean_obj_tag(v___x_1757_) == 0 {
                    v_a_1758_ = leanh::lean_ctor_get(v___x_1757_, 0);
                    leanh::lean_inc(v_a_1758_);
                    leanh::lean_dec_ref_known(v___x_1757_, 1);
                    v___x_1759_ = lean_st_ref_get(v_a_1748_);
                    v_mvarId_1760_ = leanh::lean_ctor_get(v___x_1759_, 0);
                    leanh::lean_inc(v_mvarId_1760_);
                    leanh::lean_dec(v___x_1759_);
                    v___x_1761_ = l_Lean_MVarId_getNondepPropHyps(
                        v_mvarId_1760_,
                        v_a_1749_,
                        v_a_1750_,
                        v_a_1751_,
                        v_a_1752_,
                    );
                    if leanh::lean_obj_tag(v___x_1761_) == 0 {
                        v_a_1762_ = leanh::lean_ctor_get(v___x_1761_, 0);
                        leanh::lean_inc(v_a_1762_);
                        leanh::lean_dec_ref_known(v___x_1761_, 1);
                        v___x_1763_ = lean_st_ref_get(v_a_1748_);
                        v_ctx_1764_ = leanh::lean_ctor_get(v___x_1763_, 2);
                        leanh::lean_inc_ref(v_ctx_1764_);
                        leanh::lean_dec(v___x_1763_);
                        v_simpTheorems_1765_ = leanh::lean_ctor_get(v_ctx_1764_, 6);
                        leanh::lean_inc_ref(v_simpTheorems_1765_);
                        leanh::lean_dec_ref(v_ctx_1764_);
                        v_sz_1766_ = lean_array_size(v_a_1758_);
                        v___x_1767_ = 0usize;
                        v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_1762_, v_a_1758_, v_sz_1766_, v___x_1767_, v_simpTheorems_1765_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
                        leanh::lean_dec(v_a_1758_);
                        leanh::lean_dec(v_a_1762_);
                        if leanh::lean_obj_tag(v___x_1768_) == 0 {
                            v_isSharedCheck_1776_ =
                                (!leanh::lean_is_exclusive(v___x_1768_)) as u8;
                            if v_isSharedCheck_1776_ == 0 {
                                v_unused_1777_ = leanh::lean_ctor_get(v___x_1768_, 0);
                                leanh::lean_dec(v_unused_1777_);
                                v___x_1770_ = v___x_1768_;
                                v_isShared_1771_ = v_isSharedCheck_1776_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1768_);
                                v___x_1770_ = leanh::lean_box(0);
                                v_isShared_1771_ = v_isSharedCheck_1776_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1778_ = leanh::lean_ctor_get(v___x_1768_, 0);
                            v_isSharedCheck_1785_ =
                                (!leanh::lean_is_exclusive(v___x_1768_)) as u8;
                            if v_isSharedCheck_1785_ == 0 {
                                v___x_1780_ = v___x_1768_;
                                v_isShared_1781_ = v_isSharedCheck_1785_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1778_);
                                leanh::lean_dec(v___x_1768_);
                                v___x_1780_ = leanh::lean_box(0);
                                v_isShared_1781_ = v_isSharedCheck_1785_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1758_);
                        v_a_1786_ = leanh::lean_ctor_get(v___x_1761_, 0);
                        v_isSharedCheck_1793_ =
                            (!leanh::lean_is_exclusive(v___x_1761_)) as u8;
                        if v_isSharedCheck_1793_ == 0 {
                            v___x_1788_ = v___x_1761_;
                            v_isShared_1789_ = v_isSharedCheck_1793_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1786_);
                            leanh::lean_dec(v___x_1761_);
                            v___x_1788_ = leanh::lean_box(0);
                            v_isShared_1789_ = v_isSharedCheck_1793_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_1794_ = leanh::lean_ctor_get(v___x_1757_, 0);
                    v_isSharedCheck_1801_ = (!leanh::lean_is_exclusive(v___x_1757_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1757_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1794_);
                        leanh::lean_dec(v___x_1757_);
                        v___x_1796_ = leanh::lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1772_ = leanh::lean_box(0);
                if v_isShared_1771_ == 0 {
                    leanh::lean_ctor_set(v___x_1770_, 0, v___x_1772_);
                    v___x_1774_ = v___x_1770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1774_;
            }
            3 => {
                if v_isShared_1781_ == 0 {
                    v___x_1783_ = v___x_1780_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1783_;
            }
            5 => {
                if v_isShared_1789_ == 0 {
                    v___x_1791_ = v___x_1788_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
                    v___x_1791_ = v_reuseFailAlloc_1792_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1791_;
            }
            7 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(
    mut v_a_1802_: *mut leanh::LeanObject,
    mut v_a_1803_: *mut leanh::LeanObject,
    mut v_a_1804_: *mut leanh::LeanObject,
    mut v_a_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
    mut v_a_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1808_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(
        v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_,
    );
    leanh::lean_dec(v_a_1806_);
    leanh::lean_dec_ref(v_a_1805_);
    leanh::lean_dec(v_a_1804_);
    leanh::lean_dec_ref(v_a_1803_);
    leanh::lean_dec(v_a_1802_);
    return v_res_1808_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(
    mut v_a_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpTheorems_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = lean_st_ref_get(v_a_1809_);
    v_ctx_1812_ = leanh::lean_ctor_get(v___x_1811_, 2);
    leanh::lean_inc_ref(v_ctx_1812_);
    leanh::lean_dec(v___x_1811_);
    v_simpTheorems_1813_ = leanh::lean_ctor_get(v_ctx_1812_, 6);
    leanh::lean_inc_ref(v_simpTheorems_1813_);
    leanh::lean_dec_ref(v_ctx_1812_);
    v___x_1814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1814_, 0, v_simpTheorems_1813_);
    return v___x_1814_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg___boxed(
    mut v_a_1815_: *mut leanh::LeanObject,
    mut v_a_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ =
        l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(
            v_a_1815_,
        );
    leanh::lean_dec(v_a_1815_);
    return v_res_1817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(
    mut v_a_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpTheorems_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1824_ = lean_st_ref_get(v_a_1818_);
    v_ctx_1825_ = leanh::lean_ctor_get(v___x_1824_, 2);
    leanh::lean_inc_ref(v_ctx_1825_);
    leanh::lean_dec(v___x_1824_);
    v_simpTheorems_1826_ = leanh::lean_ctor_get(v_ctx_1825_, 6);
    leanh::lean_inc_ref(v_simpTheorems_1826_);
    leanh::lean_dec_ref(v_ctx_1825_);
    v___x_1827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1827_, 0, v_simpTheorems_1826_);
    return v___x_1827_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(
    mut v_a_1828_: *mut leanh::LeanObject,
    mut v_a_1829_: *mut leanh::LeanObject,
    mut v_a_1830_: *mut leanh::LeanObject,
    mut v_a_1831_: *mut leanh::LeanObject,
    mut v_a_1832_: *mut leanh::LeanObject,
    mut v_a_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(
        v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_,
    );
    leanh::lean_dec(v_a_1832_);
    leanh::lean_dec_ref(v_a_1831_);
    leanh::lean_dec(v_a_1830_);
    leanh::lean_dec_ref(v_a_1829_);
    leanh::lean_dec(v_a_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(
    mut v___y_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v_r_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut v_unused_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1837_ = lean_st_ref_get(v___y_1835_);
                v_ngen_1838_ = leanh::lean_ctor_get(v___x_1837_, 2);
                leanh::lean_inc_ref(v_ngen_1838_);
                leanh::lean_dec(v___x_1837_);
                v_namePrefix_1839_ = leanh::lean_ctor_get(v_ngen_1838_, 0);
                v_idx_1840_ = leanh::lean_ctor_get(v_ngen_1838_, 1);
                v_isSharedCheck_1869_ = (!leanh::lean_is_exclusive(v_ngen_1838_)) as u8;
                if v_isSharedCheck_1869_ == 0 {
                    v___x_1842_ = v_ngen_1838_;
                    v_isShared_1843_ = v_isSharedCheck_1869_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_1840_);
                    leanh::lean_inc(v_namePrefix_1839_);
                    leanh::lean_dec(v_ngen_1838_);
                    v___x_1842_ = leanh::lean_box(0);
                    v_isShared_1843_ = v_isSharedCheck_1869_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1844_ = lean_st_ref_take(v___y_1835_);
                v_env_1845_ = leanh::lean_ctor_get(v___x_1844_, 0);
                v_nextMacroScope_1846_ = leanh::lean_ctor_get(v___x_1844_, 1);
                v_auxDeclNGen_1847_ = leanh::lean_ctor_get(v___x_1844_, 3);
                v_traceState_1848_ = leanh::lean_ctor_get(v___x_1844_, 4);
                v_cache_1849_ = leanh::lean_ctor_get(v___x_1844_, 5);
                v_messages_1850_ = leanh::lean_ctor_get(v___x_1844_, 6);
                v_infoState_1851_ = leanh::lean_ctor_get(v___x_1844_, 7);
                v_snapshotTasks_1852_ = leanh::lean_ctor_get(v___x_1844_, 8);
                v_isSharedCheck_1867_ = (!leanh::lean_is_exclusive(v___x_1844_)) as u8;
                if v_isSharedCheck_1867_ == 0 {
                    v_unused_1868_ = leanh::lean_ctor_get(v___x_1844_, 2);
                    leanh::lean_dec(v_unused_1868_);
                    v___x_1854_ = v___x_1844_;
                    v_isShared_1855_ = v_isSharedCheck_1867_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1852_);
                    leanh::lean_inc(v_infoState_1851_);
                    leanh::lean_inc(v_messages_1850_);
                    leanh::lean_inc(v_cache_1849_);
                    leanh::lean_inc(v_traceState_1848_);
                    leanh::lean_inc(v_auxDeclNGen_1847_);
                    leanh::lean_inc(v_nextMacroScope_1846_);
                    leanh::lean_inc(v_env_1845_);
                    leanh::lean_dec(v___x_1844_);
                    v___x_1854_ = leanh::lean_box(0);
                    v_isShared_1855_ = v_isSharedCheck_1867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_1840_);
                leanh::lean_inc(v_namePrefix_1839_);
                v_r_1856_ = l_Lean_Name_num___override(v_namePrefix_1839_, v_idx_1840_);
                v___x_1857_ = leanh::lean_unsigned_to_nat(1);
                v___x_1858_ = lean_nat_add(v_idx_1840_, v___x_1857_);
                leanh::lean_dec(v_idx_1840_);
                if v_isShared_1843_ == 0 {
                    leanh::lean_ctor_set(v___x_1842_, 1, v___x_1858_);
                    v___x_1860_ = v___x_1842_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_namePrefix_1839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1858_);
                    v___x_1860_ = v_reuseFailAlloc_1866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1855_ == 0 {
                    leanh::lean_ctor_set(v___x_1854_, 2, v___x_1860_);
                    v___x_1862_ = v___x_1854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_env_1845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_nextMacroScope_1846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 2, v___x_1860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_auxDeclNGen_1847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_traceState_1848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 5, v_cache_1849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 6, v_messages_1850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 7, v_infoState_1851_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 8, v_snapshotTasks_1852_);
                    v___x_1862_ = v_reuseFailAlloc_1865_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1863_ = lean_st_ref_set(v___y_1835_, v___x_1862_);
                v___x_1864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1864_, 0, v_r_1856_);
                return v___x_1864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg___boxed(
    mut v___y_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_1870_);
    leanh::lean_dec(v___y_1870_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(
    mut v___y_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_1877_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___boxed(
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
    leanh::lean_dec(v___y_1884_);
    leanh::lean_dec_ref(v___y_1883_);
    leanh::lean_dec(v___y_1882_);
    leanh::lean_dec_ref(v___y_1881_);
    leanh::lean_dec(v___y_1880_);
    return v_res_1886_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0;
    v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
    return v___x_1889_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2;
    v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4;
    v___x_1895_ = l_Lean_stringToMessageData(v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(
    mut v_x_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_1899_: u8 = 0;
    let mut v_inv_1900_: u8 = 0;
    let mut v___x_1901_: u8 = 0;
    let mut v_r_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v_ref_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1929_: u8 = 0;
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1896_) {
                0 => {
                    v_declName_1898_ = leanh::lean_ctor_get(v_x_1896_, 0);
                    leanh::lean_inc(v_declName_1898_);
                    v_post_1899_ = leanh::lean_ctor_get_uint8(
                        v_x_1896_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_inv_1900_ = leanh::lean_ctor_get_uint8(
                        v_x_1896_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_1896_, 1);
                    v___x_1901_ = 0;
                    v_r_1902_ = l_Lean_MessageData_ofConstName(v_declName_1898_, v___x_1901_);
                    if v_post_1899_ == 0 {
                        if v_inv_1900_ == 0 {
                            v___x_1903_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1);
                            v___x_1904_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1904_, 0, v___x_1903_);
                            leanh::lean_ctor_set(v___x_1904_, 1, v_r_1902_);
                            v___x_1905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                            return v___x_1905_;
                        } else {
                            v___x_1906_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3);
                            v___x_1907_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1907_, 0, v___x_1906_);
                            leanh::lean_ctor_set(v___x_1907_, 1, v_r_1902_);
                            v___x_1908_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
                            return v___x_1908_;
                        }
                    } else {
                        if v_inv_1900_ == 0 {
                            v___x_1909_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1909_, 0, v_r_1902_);
                            return v___x_1909_;
                        } else {
                            v___x_1910_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5);
                            v___x_1911_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1911_, 0, v___x_1910_);
                            leanh::lean_ctor_set(v___x_1911_, 1, v_r_1902_);
                            v___x_1912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1912_, 0, v___x_1911_);
                            return v___x_1912_;
                        }
                    }
                }
                1 => {
                    v_fvarId_1913_ = leanh::lean_ctor_get(v_x_1896_, 0);
                    v_isSharedCheck_1922_ = (!leanh::lean_is_exclusive(v_x_1896_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v___x_1915_ = v_x_1896_;
                        v_isShared_1916_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_1913_);
                        leanh::lean_dec(v_x_1896_);
                        v___x_1915_ = leanh::lean_box(0);
                        v_isShared_1916_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ref_1923_ = leanh::lean_ctor_get(v_x_1896_, 1);
                    leanh::lean_inc(v_ref_1923_);
                    leanh::lean_dec_ref_known(v_x_1896_, 2);
                    v___x_1924_ = l_Lean_MessageData_ofSyntax(v_ref_1923_);
                    v___x_1925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                    return v___x_1925_;
                }
                _ => {
                    v_name_1926_ = leanh::lean_ctor_get(v_x_1896_, 0);
                    v_isSharedCheck_1934_ = (!leanh::lean_is_exclusive(v_x_1896_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1928_ = v_x_1896_;
                        v_isShared_1929_ = v_isSharedCheck_1934_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_1926_);
                        leanh::lean_dec(v_x_1896_);
                        v___x_1928_ = leanh::lean_box(0);
                        v_isShared_1929_ = v_isSharedCheck_1934_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1917_ = l_Lean_mkFVar(v_fvarId_1913_);
                v___x_1918_ = l_Lean_MessageData_ofExpr(v___x_1917_);
                if v_isShared_1916_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1915_, 0);
                    leanh::lean_ctor_set(v___x_1915_, 0, v___x_1918_);
                    v___x_1920_ = v___x_1915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
                    v___x_1920_ = v_reuseFailAlloc_1921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1920_;
            }
            3 => {
                v___x_1930_ = l_Lean_MessageData_ofName(v_name_1926_);
                if v_isShared_1929_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1928_, 0);
                    leanh::lean_ctor_set(v___x_1928_, 0, v___x_1930_);
                    v___x_1932_ = v___x_1928_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
                    v___x_1932_ = v_reuseFailAlloc_1933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(
    mut v_x_1935_: *mut leanh::LeanObject,
    mut v___y_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_1935_);
    return v_res_1937_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(
    mut v_x_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_1938_);
    return v___x_1945_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(
    mut v_x_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1953_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(v_x_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
    leanh::lean_dec(v___y_1951_);
    leanh::lean_dec_ref(v___y_1950_);
    leanh::lean_dec(v___y_1949_);
    leanh::lean_dec_ref(v___y_1948_);
    leanh::lean_dec(v___y_1947_);
    return v_res_1953_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(
    mut v_msgData_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_st_ref_get(v___y_1958_);
    v_env_1961_ = leanh::lean_ctor_get(v___x_1960_, 0);
    leanh::lean_inc_ref(v_env_1961_);
    leanh::lean_dec(v___x_1960_);
    v___x_1962_ = lean_st_ref_get(v___y_1956_);
    v_mctx_1963_ = leanh::lean_ctor_get(v___x_1962_, 0);
    leanh::lean_inc_ref(v_mctx_1963_);
    leanh::lean_dec(v___x_1962_);
    v_lctx_1964_ = leanh::lean_ctor_get(v___y_1955_, 2);
    v_options_1965_ = leanh::lean_ctor_get(v___y_1957_, 2);
    leanh::lean_inc_ref(v_options_1965_);
    leanh::lean_inc_ref(v_lctx_1964_);
    v___x_1966_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1966_, 0, v_env_1961_);
    leanh::lean_ctor_set(v___x_1966_, 1, v_mctx_1963_);
    leanh::lean_ctor_set(v___x_1966_, 2, v_lctx_1964_);
    leanh::lean_ctor_set(v___x_1966_, 3, v_options_1965_);
    v___x_1967_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    leanh::lean_ctor_set(v___x_1967_, 1, v_msgData_1954_);
    v___x_1968_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(
    mut v_msgData_1969_: *mut leanh::LeanObject,
    mut v___y_1970_: *mut leanh::LeanObject,
    mut v___y_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
    leanh::lean_dec(v___y_1973_);
    leanh::lean_dec_ref(v___y_1972_);
    leanh::lean_dec(v___y_1971_);
    leanh::lean_dec_ref(v___y_1970_);
    return v_res_1975_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: f64 = 0.0;
    v___x_1976_ = leanh::lean_unsigned_to_nat(0);
    v___x_1977_ = lean_float_of_nat(v___x_1976_);
    return v___x_1977_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(
    mut v_cls_1981_: *mut leanh::LeanObject,
    mut v_msg_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v_tid_2007_: u64 = 0;
    let mut v_traces_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: f64 = 0.0;
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1988_ = leanh::lean_ctor_get(v___y_1985_, 5);
                v___x_1989_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
                v_a_1990_ = leanh::lean_ctor_get(v___x_1989_, 0);
                v_isSharedCheck_2034_ = (!leanh::lean_is_exclusive(v___x_1989_)) as u8;
                if v_isSharedCheck_2034_ == 0 {
                    v___x_1992_ = v___x_1989_;
                    v_isShared_1993_ = v_isSharedCheck_2034_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1990_);
                    leanh::lean_dec(v___x_1989_);
                    v___x_1992_ = leanh::lean_box(0);
                    v_isShared_1993_ = v_isSharedCheck_2034_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1994_ = lean_st_ref_take(v___y_1986_);
                v_traceState_1995_ = leanh::lean_ctor_get(v___x_1994_, 4);
                v_env_1996_ = leanh::lean_ctor_get(v___x_1994_, 0);
                v_nextMacroScope_1997_ = leanh::lean_ctor_get(v___x_1994_, 1);
                v_ngen_1998_ = leanh::lean_ctor_get(v___x_1994_, 2);
                v_auxDeclNGen_1999_ = leanh::lean_ctor_get(v___x_1994_, 3);
                v_cache_2000_ = leanh::lean_ctor_get(v___x_1994_, 5);
                v_messages_2001_ = leanh::lean_ctor_get(v___x_1994_, 6);
                v_infoState_2002_ = leanh::lean_ctor_get(v___x_1994_, 7);
                v_snapshotTasks_2003_ = leanh::lean_ctor_get(v___x_1994_, 8);
                v_isSharedCheck_2033_ = (!leanh::lean_is_exclusive(v___x_1994_)) as u8;
                if v_isSharedCheck_2033_ == 0 {
                    v___x_2005_ = v___x_1994_;
                    v_isShared_2006_ = v_isSharedCheck_2033_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2003_);
                    leanh::lean_inc(v_infoState_2002_);
                    leanh::lean_inc(v_messages_2001_);
                    leanh::lean_inc(v_cache_2000_);
                    leanh::lean_inc(v_traceState_1995_);
                    leanh::lean_inc(v_auxDeclNGen_1999_);
                    leanh::lean_inc(v_ngen_1998_);
                    leanh::lean_inc(v_nextMacroScope_1997_);
                    leanh::lean_inc(v_env_1996_);
                    leanh::lean_dec(v___x_1994_);
                    v___x_2005_ = leanh::lean_box(0);
                    v_isShared_2006_ = v_isSharedCheck_2033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2007_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1995_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2008_ = leanh::lean_ctor_get(v_traceState_1995_, 0);
                v_isSharedCheck_2032_ =
                    (!leanh::lean_is_exclusive(v_traceState_1995_)) as u8;
                if v_isSharedCheck_2032_ == 0 {
                    v___x_2010_ = v_traceState_1995_;
                    v_isShared_2011_ = v_isSharedCheck_2032_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_2008_);
                    leanh::lean_dec(v_traceState_1995_);
                    v___x_2010_ = leanh::lean_box(0);
                    v_isShared_2011_ = v_isSharedCheck_2032_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2012_ = leanh::lean_box(0);
                v___x_2013_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0);
                v___x_2014_ = 0;
                v___x_2015_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1;
                v___x_2016_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_2016_, 0, v_cls_1981_);
                leanh::lean_ctor_set(v___x_2016_, 1, v___x_2012_);
                leanh::lean_ctor_set(v___x_2016_, 2, v___x_2015_);
                leanh::lean_ctor_set_float(
                    v___x_2016_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2013_,
                );
                leanh::lean_ctor_set_float(
                    v___x_2016_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2013_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2016_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2014_,
                );
                v___x_2017_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2;
                v___x_2018_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2018_, 0, v___x_2016_);
                leanh::lean_ctor_set(v___x_2018_, 1, v_a_1990_);
                leanh::lean_ctor_set(v___x_2018_, 2, v___x_2017_);
                leanh::lean_inc(v_ref_1988_);
                v___x_2019_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2019_, 0, v_ref_1988_);
                leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
                v___x_2020_ = l_Lean_PersistentArray_push___redArg(v_traces_2008_, v___x_2019_);
                if v_isShared_2011_ == 0 {
                    leanh::lean_ctor_set(v___x_2010_, 0, v___x_2020_);
                    v___x_2022_ = v___x_2010_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2020_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2031_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2007_,
                    );
                    v___x_2022_ = v_reuseFailAlloc_2031_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2006_ == 0 {
                    leanh::lean_ctor_set(v___x_2005_, 4, v___x_2022_);
                    v___x_2024_ = v___x_2005_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_env_1996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_nextMacroScope_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_ngen_1998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 3, v_auxDeclNGen_1999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 4, v___x_2022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 5, v_cache_2000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 6, v_messages_2001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 7, v_infoState_2002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 8, v_snapshotTasks_2003_);
                    v___x_2024_ = v_reuseFailAlloc_2030_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2025_ = lean_st_ref_set(v___y_1986_, v___x_2024_);
                v___x_2026_ = leanh::lean_box(0);
                if v_isShared_1993_ == 0 {
                    leanh::lean_ctor_set(v___x_1992_, 0, v___x_2026_);
                    v___x_2028_ = v___x_1992_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(
    mut v_cls_2035_: *mut leanh::LeanObject,
    mut v_msg_2036_: *mut leanh::LeanObject,
    mut v___y_2037_: *mut leanh::LeanObject,
    mut v___y_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v___y_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_2035_, v_msg_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
    leanh::lean_dec(v___y_2040_);
    leanh::lean_dec_ref(v___y_2039_);
    leanh::lean_dec(v___y_2038_);
    leanh::lean_dec_ref(v___y_2037_);
    return v_res_2042_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(
    mut v_fst_2043_: *mut leanh::LeanObject,
    mut v_snd_2044_: *mut leanh::LeanObject,
    mut v___x_2045_: *mut leanh::LeanObject,
    mut v_fvarId_2046_: *mut leanh::LeanObject,
    mut v___x_2047_: u8,
    mut v___x_2048_: *mut leanh::LeanObject,
    mut v_a_2049_: *mut leanh::LeanObject,
    mut v___x_2050_: *mut leanh::LeanObject,
    mut v_userName_2051_: *mut leanh::LeanObject,
    mut v_origType_2052_: *mut leanh::LeanObject,
    mut v_____r_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpTheorems_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexConfig_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___y_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v_xs_x27_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_unused_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2103_: u8 = 0;
    let mut v_a_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_a_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2119_: u8 = 0;
    let mut v_a_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2060_ = lean_st_ref_get(v___y_2054_);
                v___x_2061_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_2058_);
                if leanh::lean_obj_tag(v___x_2061_) == 0 {
                    v_a_2062_ = leanh::lean_ctor_get(v___x_2061_, 0);
                    leanh::lean_inc(v_a_2062_);
                    leanh::lean_dec_ref_known(v___x_2061_, 1);
                    leanh::lean_inc_ref(v_snd_2044_);
                    leanh::lean_inc_ref(v_fst_2043_);
                    v___x_2063_ = l_Lean_Meta_mkExpectedTypeHint(
                        v_fst_2043_,
                        v_snd_2044_,
                        v___y_2055_,
                        v___y_2056_,
                        v___y_2057_,
                        v___y_2058_,
                    );
                    if leanh::lean_obj_tag(v___x_2063_) == 0 {
                        v_ctx_2064_ = leanh::lean_ctor_get(v___x_2060_, 2);
                        leanh::lean_inc_ref(v_ctx_2064_);
                        leanh::lean_dec(v___x_2060_);
                        v_a_2065_ = leanh::lean_ctor_get(v___x_2063_, 0);
                        leanh::lean_inc(v_a_2065_);
                        leanh::lean_dec_ref_known(v___x_2063_, 1);
                        v_simpTheorems_2066_ = leanh::lean_ctor_get(v_ctx_2064_, 6);
                        leanh::lean_inc_ref(v_simpTheorems_2066_);
                        leanh::lean_dec_ref(v_ctx_2064_);
                        v_indexConfig_2067_ = leanh::lean_ctor_get(v___x_2045_, 5);
                        leanh::lean_inc(v_fvarId_2046_);
                        v___x_2068_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2068_, 0, v_fvarId_2046_);
                        v___x_2069_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(
                            v_simpTheorems_2066_,
                            v___x_2068_,
                        );
                        v___x_2070_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2070_, 0, v_a_2062_);
                        leanh::lean_inc_ref(v_indexConfig_2067_);
                        leanh::lean_inc_ref(v___x_2070_);
                        v___x_2071_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                            v___x_2069_,
                            v___x_2070_,
                            v_a_2065_,
                            v_indexConfig_2067_,
                            v___y_2055_,
                            v___y_2056_,
                            v___y_2057_,
                            v___y_2058_,
                        );
                        if leanh::lean_obj_tag(v___x_2071_) == 0 {
                            v_a_2072_ = leanh::lean_ctor_get(v___x_2071_, 0);
                            v_isSharedCheck_2103_ =
                                (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                            if v_isSharedCheck_2103_ == 0 {
                                v___x_2074_ = v___x_2071_;
                                v_isShared_2075_ = v_isSharedCheck_2103_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2072_);
                                leanh::lean_dec(v___x_2071_);
                                v___x_2074_ = leanh::lean_box(0);
                                v_isShared_2075_ = v_isSharedCheck_2103_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_2070_, 1);
                            leanh::lean_dec_ref(v_origType_2052_);
                            leanh::lean_dec(v_userName_2051_);
                            leanh::lean_dec_ref(v___x_2048_);
                            leanh::lean_dec(v_fvarId_2046_);
                            leanh::lean_dec_ref(v___x_2045_);
                            leanh::lean_dec_ref(v_snd_2044_);
                            leanh::lean_dec_ref(v_fst_2043_);
                            v_a_2104_ = leanh::lean_ctor_get(v___x_2071_, 0);
                            v_isSharedCheck_2111_ =
                                (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                            if v_isSharedCheck_2111_ == 0 {
                                v___x_2106_ = v___x_2071_;
                                v_isShared_2107_ = v_isSharedCheck_2111_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2104_);
                                leanh::lean_dec(v___x_2071_);
                                v___x_2106_ = leanh::lean_box(0);
                                v_isShared_2107_ = v_isSharedCheck_2111_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2062_);
                        leanh::lean_dec(v___x_2060_);
                        leanh::lean_dec_ref(v_origType_2052_);
                        leanh::lean_dec(v_userName_2051_);
                        leanh::lean_dec_ref(v___x_2048_);
                        leanh::lean_dec(v_fvarId_2046_);
                        leanh::lean_dec_ref(v___x_2045_);
                        leanh::lean_dec_ref(v_snd_2044_);
                        leanh::lean_dec_ref(v_fst_2043_);
                        v_a_2112_ = leanh::lean_ctor_get(v___x_2063_, 0);
                        v_isSharedCheck_2119_ =
                            (!leanh::lean_is_exclusive(v___x_2063_)) as u8;
                        if v_isSharedCheck_2119_ == 0 {
                            v___x_2114_ = v___x_2063_;
                            v_isShared_2115_ = v_isSharedCheck_2119_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2112_);
                            leanh::lean_dec(v___x_2063_);
                            v___x_2114_ = leanh::lean_box(0);
                            v_isShared_2115_ = v_isSharedCheck_2119_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2060_);
                    leanh::lean_dec_ref(v_origType_2052_);
                    leanh::lean_dec(v_userName_2051_);
                    leanh::lean_dec_ref(v___x_2048_);
                    leanh::lean_dec(v_fvarId_2046_);
                    leanh::lean_dec_ref(v___x_2045_);
                    leanh::lean_dec_ref(v_snd_2044_);
                    leanh::lean_dec_ref(v_fst_2043_);
                    v_a_2120_ = leanh::lean_ctor_get(v___x_2061_, 0);
                    v_isSharedCheck_2127_ = (!leanh::lean_is_exclusive(v___x_2061_)) as u8;
                    if v_isSharedCheck_2127_ == 0 {
                        v___x_2122_ = v___x_2061_;
                        v_isShared_2123_ = v_isSharedCheck_2127_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2120_);
                        leanh::lean_dec(v___x_2061_);
                        v___x_2122_ = leanh::lean_box(0);
                        v_isShared_2123_ = v_isSharedCheck_2127_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2076_ = lean_st_ref_take(v___y_2054_);
                v_mvarId_2077_ = leanh::lean_ctor_get(v___x_2076_, 0);
                v_entries_2078_ = leanh::lean_ctor_get(v___x_2076_, 1);
                v_simprocs_2079_ = leanh::lean_ctor_get(v___x_2076_, 3);
                v_usedTheorems_2080_ = leanh::lean_ctor_get(v___x_2076_, 4);
                v_diag_2081_ = leanh::lean_ctor_get(v___x_2076_, 5);
                v_isSharedCheck_2101_ = (!leanh::lean_is_exclusive(v___x_2076_)) as u8;
                if v_isSharedCheck_2101_ == 0 {
                    v_unused_2102_ = leanh::lean_ctor_get(v___x_2076_, 2);
                    leanh::lean_dec(v_unused_2102_);
                    v___x_2083_ = v___x_2076_;
                    v_isShared_2084_ = v_isSharedCheck_2101_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2081_);
                    leanh::lean_inc(v_usedTheorems_2080_);
                    leanh::lean_inc(v_simprocs_2079_);
                    leanh::lean_inc(v_entries_2078_);
                    leanh::lean_inc(v_mvarId_2077_);
                    leanh::lean_dec(v___x_2076_);
                    v___x_2083_ = leanh::lean_box(0);
                    v_isShared_2084_ = v_isSharedCheck_2101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2096_ = lean_array_get_size(v_entries_2078_);
                v___x_2097_ = lean_nat_dec_lt(v_a_2049_, v___x_2096_);
                if v___x_2097_ == 0 {
                    leanh::lean_dec_ref_known(v___x_2070_, 1);
                    leanh::lean_dec_ref(v_origType_2052_);
                    leanh::lean_dec(v_userName_2051_);
                    leanh::lean_dec(v_fvarId_2046_);
                    leanh::lean_dec_ref(v_snd_2044_);
                    leanh::lean_dec_ref(v_fst_2043_);
                    v___y_2086_ = v_entries_2078_;
                    state = 3;
                    continue;
                } else {
                    v_xs_x27_2098_ = lean_array_fset(v_entries_2078_, v_a_2049_, v___x_2050_);
                    v___x_2099_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v___x_2099_, 0, v_fvarId_2046_);
                    leanh::lean_ctor_set(v___x_2099_, 1, v_userName_2051_);
                    leanh::lean_ctor_set(v___x_2099_, 2, v___x_2070_);
                    leanh::lean_ctor_set(v___x_2099_, 3, v_origType_2052_);
                    leanh::lean_ctor_set(v___x_2099_, 4, v_snd_2044_);
                    leanh::lean_ctor_set(v___x_2099_, 5, v_fst_2043_);
                    v___x_2100_ = lean_array_fset(v_xs_x27_2098_, v_a_2049_, v___x_2099_);
                    v___y_2086_ = v___x_2100_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2087_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_2045_, v_a_2072_);
                if v_isShared_2084_ == 0 {
                    leanh::lean_ctor_set(v___x_2083_, 2, v___x_2087_);
                    leanh::lean_ctor_set(v___x_2083_, 1, v___y_2086_);
                    v___x_2089_ = v___x_2083_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_mvarId_2077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___y_2086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 2, v___x_2087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_simprocs_2079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_usedTheorems_2080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 5, v_diag_2081_);
                    v___x_2089_ = v_reuseFailAlloc_2095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2089_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_2047_,
                );
                v___x_2090_ = lean_st_ref_set(v___y_2054_, v___x_2089_);
                v___x_2091_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2091_, 0, v___x_2048_);
                if v_isShared_2075_ == 0 {
                    leanh::lean_ctor_set(v___x_2074_, 0, v___x_2091_);
                    v___x_2093_ = v___x_2074_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
                    v___x_2093_ = v_reuseFailAlloc_2094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2093_;
            }
            6 => {
                if v_isShared_2107_ == 0 {
                    v___x_2109_ = v___x_2106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
                    v___x_2109_ = v_reuseFailAlloc_2110_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2109_;
            }
            8 => {
                if v_isShared_2115_ == 0 {
                    v___x_2117_ = v___x_2114_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
                    v___x_2117_ = v_reuseFailAlloc_2118_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2117_;
            }
            10 => {
                if v_isShared_2123_ == 0 {
                    v___x_2125_ = v___x_2122_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
                    v___x_2125_ = v_reuseFailAlloc_2126_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2128_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_snd_2129_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_2130_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_fvarId_2131_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_2132_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2133_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_2134_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2135_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_userName_2136_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_origType_2137_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_____r_2138_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_2139_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_2140_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_2141_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_2142_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_2143_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_2144_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_27646__boxed_2145_: u8 = 0;
    let mut v_res_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_27646__boxed_2145_ = (leanh::lean_unbox(v___x_2132_) as u8);
    v_res_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_2128_, v_snd_2129_, v___x_2130_, v_fvarId_2131_, v___x_27646__boxed_2145_, v___x_2133_, v_a_2134_, v___x_2135_, v_userName_2136_, v_origType_2137_, v_____r_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
    leanh::lean_dec(v___y_2143_);
    leanh::lean_dec_ref(v___y_2142_);
    leanh::lean_dec(v___y_2141_);
    leanh::lean_dec_ref(v___y_2140_);
    leanh::lean_dec(v___y_2139_);
    leanh::lean_dec(v_a_2134_);
    return v_res_2146_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5;
    v___x_2163_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7;
    v___x_2164_ = l_Lean_Name_append(v___x_2163_, v___x_2162_);
    return v___x_2164_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9;
    v___x_2167_ = l_Lean_stringToMessageData(v___x_2166_);
    return v___x_2167_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11;
    v___x_2170_ = l_Lean_stringToMessageData(v___x_2169_);
    return v___x_2170_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13;
    v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
    return v___x_2173_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(
    mut v_upperBound_2174_: *mut leanh::LeanObject,
    mut v___x_2175_: *mut leanh::LeanObject,
    mut v___x_2176_: *mut leanh::LeanObject,
    mut v_a_2177_: *mut leanh::LeanObject,
    mut v_b_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v_a_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut v_a_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpTheorems_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origType_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2237_: u8 = 0;
    let mut v_fst_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_2244_: u8 = 0;
    let mut v_mvarId_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2251_: u8 = 0;
    let mut v_usedTheorems_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: u8 = 0;
    let mut v_options_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2279_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v_reuseFailAlloc_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_unused_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut v_a_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2210_ = lean_nat_dec_lt(v_a_2177_, v_upperBound_2174_);
                if v___x_2210_ == 0 {
                    leanh::lean_dec(v_a_2177_);
                    leanh::lean_dec_ref(v___x_2176_);
                    v___x_2211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2211_, 0, v_b_2178_);
                    return v___x_2211_;
                } else {
                    leanh::lean_dec_ref(v_b_2178_);
                    v___x_2212_ = lean_st_ref_get(v___y_2179_);
                    v___x_2213_ = lean_st_ref_get(v___y_2179_);
                    v___x_2214_ = lean_st_ref_get(v___y_2179_);
                    v___x_2215_ = lean_st_ref_get(v___y_2179_);
                    v_ctx_2216_ = leanh::lean_ctor_get(v___x_2213_, 2);
                    leanh::lean_inc_ref(v_ctx_2216_);
                    leanh::lean_dec(v___x_2213_);
                    v_ctx_2217_ = leanh::lean_ctor_get(v___x_2212_, 2);
                    leanh::lean_inc_ref(v_ctx_2217_);
                    leanh::lean_dec(v___x_2212_);
                    v_simpTheorems_2218_ = leanh::lean_ctor_get(v_ctx_2216_, 6);
                    leanh::lean_inc_ref(v_simpTheorems_2218_);
                    leanh::lean_dec_ref(v_ctx_2216_);
                    v___x_2219_ = lean_array_fget_borrowed(v___x_2175_, v_a_2177_);
                    v_fvarId_2220_ = leanh::lean_ctor_get(v___x_2219_, 0);
                    v_userName_2221_ = leanh::lean_ctor_get(v___x_2219_, 1);
                    v_id_2222_ = leanh::lean_ctor_get(v___x_2219_, 2);
                    v_origType_2223_ = leanh::lean_ctor_get(v___x_2219_, 3);
                    v_type_2224_ = leanh::lean_ctor_get(v___x_2219_, 4);
                    v_proof_2225_ = leanh::lean_ctor_get(v___x_2219_, 5);
                    v_mvarId_2226_ = leanh::lean_ctor_get(v___x_2214_, 0);
                    leanh::lean_inc(v_mvarId_2226_);
                    leanh::lean_dec(v___x_2214_);
                    v_usedTheorems_2227_ = leanh::lean_ctor_get(v___x_2215_, 4);
                    leanh::lean_inc_ref(v_usedTheorems_2227_);
                    v_diag_2228_ = leanh::lean_ctor_get(v___x_2215_, 5);
                    leanh::lean_inc_ref(v_diag_2228_);
                    leanh::lean_dec(v___x_2215_);
                    leanh::lean_inc_ref(v_id_2222_);
                    v___x_2229_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(
                        v_simpTheorems_2218_,
                        v_id_2222_,
                    );
                    v___x_2230_ =
                        l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_2217_, v___x_2229_);
                    v___x_2231_ = leanh::lean_box(0);
                    v___x_2232_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2232_, 0, v_usedTheorems_2227_);
                    leanh::lean_ctor_set(v___x_2232_, 1, v_diag_2228_);
                    leanh::lean_inc_ref(v___x_2176_);
                    leanh::lean_inc_ref(v___x_2230_);
                    leanh::lean_inc_ref(v_type_2224_);
                    leanh::lean_inc_ref(v_proof_2225_);
                    v___x_2233_ = l_Lean_Meta_simpStep(
                        v_mvarId_2226_,
                        v_proof_2225_,
                        v_type_2224_,
                        v___x_2230_,
                        v___x_2176_,
                        v___x_2231_,
                        v___x_2210_,
                        v___x_2232_,
                        v___y_2180_,
                        v___y_2181_,
                        v___y_2182_,
                        v___y_2183_,
                    );
                    leanh::lean_dec_ref_known(v___x_2232_, 2);
                    if leanh::lean_obj_tag(v___x_2233_) == 0 {
                        v_a_2234_ = leanh::lean_ctor_get(v___x_2233_, 0);
                        v_isSharedCheck_2327_ =
                            (!leanh::lean_is_exclusive(v___x_2233_)) as u8;
                        if v_isSharedCheck_2327_ == 0 {
                            v___x_2236_ = v___x_2233_;
                            v_isShared_2237_ = v_isSharedCheck_2327_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2234_);
                            leanh::lean_dec(v___x_2233_);
                            v___x_2236_ = leanh::lean_box(0);
                            v_isShared_2237_ = v_isSharedCheck_2327_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2230_);
                        leanh::lean_dec(v_a_2177_);
                        leanh::lean_dec_ref(v___x_2176_);
                        v_a_2328_ = leanh::lean_ctor_get(v___x_2233_, 0);
                        v_isSharedCheck_2335_ =
                            (!leanh::lean_is_exclusive(v___x_2233_)) as u8;
                        if v_isSharedCheck_2335_ == 0 {
                            v___x_2330_ = v___x_2233_;
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2328_);
                            leanh::lean_dec(v___x_2233_);
                            v___x_2330_ = leanh::lean_box(0);
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2187_ = leanh::lean_unsigned_to_nat(1);
                v___x_2188_ = lean_nat_add(v_a_2177_, v___x_2187_);
                leanh::lean_dec(v_a_2177_);
                v_a_2177_ = v___x_2188_;
                v_b_2178_ = v_a_2186_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_2191_) == 0 {
                    v_a_2192_ = leanh::lean_ctor_get(v___y_2191_, 0);
                    v_isSharedCheck_2201_ = (!leanh::lean_is_exclusive(v___y_2191_)) as u8;
                    if v_isSharedCheck_2201_ == 0 {
                        v___x_2194_ = v___y_2191_;
                        v_isShared_2195_ = v_isSharedCheck_2201_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2192_);
                        leanh::lean_dec(v___y_2191_);
                        v___x_2194_ = leanh::lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2201_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2177_);
                    leanh::lean_dec_ref(v___x_2176_);
                    v_a_2202_ = leanh::lean_ctor_get(v___y_2191_, 0);
                    v_isSharedCheck_2209_ = (!leanh::lean_is_exclusive(v___y_2191_)) as u8;
                    if v_isSharedCheck_2209_ == 0 {
                        v___x_2204_ = v___y_2191_;
                        v_isShared_2205_ = v_isSharedCheck_2209_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2202_);
                        leanh::lean_dec(v___y_2191_);
                        v___x_2204_ = leanh::lean_box(0);
                        v_isShared_2205_ = v_isSharedCheck_2209_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2192_) == 0 {
                    leanh::lean_dec(v_a_2177_);
                    leanh::lean_dec_ref(v___x_2176_);
                    v_a_2196_ = leanh::lean_ctor_get(v_a_2192_, 0);
                    leanh::lean_inc(v_a_2196_);
                    leanh::lean_dec_ref_known(v_a_2192_, 1);
                    if v_isShared_2195_ == 0 {
                        leanh::lean_ctor_set(v___x_2194_, 0, v_a_2196_);
                        v___x_2198_ = v___x_2194_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2199_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2196_);
                        v___x_2198_ = v_reuseFailAlloc_2199_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2194_);
                    v_a_2200_ = leanh::lean_ctor_get(v_a_2192_, 0);
                    leanh::lean_inc(v_a_2200_);
                    leanh::lean_dec_ref_known(v_a_2192_, 1);
                    v_a_2186_ = v_a_2200_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_2198_;
            }
            5 => {
                if v_isShared_2205_ == 0 {
                    v___x_2207_ = v___x_2204_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2207_;
            }
            7 => {
                v_fst_2238_ = leanh::lean_ctor_get(v_a_2234_, 0);
                v_snd_2239_ = leanh::lean_ctor_get(v_a_2234_, 1);
                v_isSharedCheck_2326_ = (!leanh::lean_is_exclusive(v_a_2234_)) as u8;
                if v_isSharedCheck_2326_ == 0 {
                    v___x_2241_ = v_a_2234_;
                    v_isShared_2242_ = v_isSharedCheck_2326_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2239_);
                    leanh::lean_inc(v_fst_2238_);
                    leanh::lean_dec(v_a_2234_);
                    v___x_2241_ = leanh::lean_box(0);
                    v_isShared_2242_ = v_isSharedCheck_2326_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2243_ = lean_st_ref_take(v___y_2179_);
                v_modified_2244_ = leanh::lean_ctor_get_uint8(
                    v___x_2243_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_mvarId_2245_ = leanh::lean_ctor_get(v___x_2243_, 0);
                v_entries_2246_ = leanh::lean_ctor_get(v___x_2243_, 1);
                v_ctx_2247_ = leanh::lean_ctor_get(v___x_2243_, 2);
                v_simprocs_2248_ = leanh::lean_ctor_get(v___x_2243_, 3);
                v_isSharedCheck_2323_ = (!leanh::lean_is_exclusive(v___x_2243_)) as u8;
                if v_isSharedCheck_2323_ == 0 {
                    v_unused_2324_ = leanh::lean_ctor_get(v___x_2243_, 5);
                    leanh::lean_dec(v_unused_2324_);
                    v_unused_2325_ = leanh::lean_ctor_get(v___x_2243_, 4);
                    leanh::lean_dec(v_unused_2325_);
                    v___x_2250_ = v___x_2243_;
                    v_isShared_2251_ = v_isSharedCheck_2323_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_simprocs_2248_);
                    leanh::lean_inc(v_ctx_2247_);
                    leanh::lean_inc(v_entries_2246_);
                    leanh::lean_inc(v_mvarId_2245_);
                    leanh::lean_dec(v___x_2243_);
                    v___x_2250_ = leanh::lean_box(0);
                    v_isShared_2251_ = v_isSharedCheck_2323_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_usedTheorems_2252_ = leanh::lean_ctor_get(v_snd_2239_, 0);
                v_diag_2253_ = leanh::lean_ctor_get(v_snd_2239_, 1);
                v_isSharedCheck_2322_ = (!leanh::lean_is_exclusive(v_snd_2239_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v___x_2255_ = v_snd_2239_;
                    v_isShared_2256_ = v_isSharedCheck_2322_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2253_);
                    leanh::lean_inc(v_usedTheorems_2252_);
                    leanh::lean_dec(v_snd_2239_);
                    v___x_2255_ = leanh::lean_box(0);
                    v_isShared_2256_ = v_isSharedCheck_2322_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2251_ == 0 {
                    leanh::lean_ctor_set(v___x_2250_, 5, v_diag_2253_);
                    leanh::lean_ctor_set(v___x_2250_, 4, v_usedTheorems_2252_);
                    v___x_2258_ = v___x_2250_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_mvarId_2245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_entries_2246_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_ctx_2247_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_simprocs_2248_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_usedTheorems_2252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_diag_2253_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2321_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_modified_2244_,
                    );
                    v___x_2258_ = v_reuseFailAlloc_2321_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2259_ = lean_st_ref_set(v___y_2179_, v___x_2258_);
                v___x_2260_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_fst_2238_) == 0 {
                    leanh::lean_del_object(v___x_2255_);
                    leanh::lean_dec_ref(v___x_2230_);
                    leanh::lean_dec(v_a_2177_);
                    leanh::lean_dec_ref(v___x_2176_);
                    v___x_2261_ = leanh::lean_box((v___x_2210_) as usize);
                    v___x_2262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2262_, 0, v___x_2261_);
                    if v_isShared_2242_ == 0 {
                        leanh::lean_ctor_set(v___x_2241_, 1, v___x_2260_);
                        leanh::lean_ctor_set(v___x_2241_, 0, v___x_2262_);
                        v___x_2264_ = v___x_2241_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2262_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2260_);
                        v___x_2264_ = v_reuseFailAlloc_2268_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2241_);
                    leanh::lean_del_object(v___x_2236_);
                    v_val_2269_ = leanh::lean_ctor_get(v_fst_2238_, 0);
                    leanh::lean_inc(v_val_2269_);
                    leanh::lean_dec_ref_known(v_fst_2238_, 1);
                    v_fst_2270_ = leanh::lean_ctor_get(v_val_2269_, 0);
                    v_snd_2271_ = leanh::lean_ctor_get(v_val_2269_, 1);
                    v_isSharedCheck_2320_ = (!leanh::lean_is_exclusive(v_val_2269_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2273_ = v_val_2269_;
                        v_isShared_2274_ = v_isSharedCheck_2320_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2271_);
                        leanh::lean_inc(v_fst_2270_);
                        leanh::lean_dec(v_val_2269_);
                        v___x_2273_ = leanh::lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2320_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2237_ == 0 {
                    leanh::lean_ctor_set(v___x_2236_, 0, v___x_2264_);
                    v___x_2266_ = v___x_2236_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
                    v___x_2266_ = v_reuseFailAlloc_2267_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2266_;
            }
            14 => {
                v___x_2275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0;
                v___x_2276_ = lean_expr_eqv(v_snd_2271_, v_type_2224_);
                if v___x_2276_ == 0 {
                    v_options_2277_ = leanh::lean_ctor_get(v___y_2182_, 2);
                    v_inheritedTraceOptions_2278_ = leanh::lean_ctor_get(v___y_2182_, 13);
                    v_hasTrace_2279_ = leanh::lean_ctor_get_uint8(
                        v_options_2277_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2279_ == 0 {
                        leanh::lean_del_object(v___x_2273_);
                        leanh::lean_del_object(v___x_2255_);
                        state = 15;
                        continue;
                    } else {
                        v___x_2282_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5;
                        v___x_2283_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8);
                        v___x_2284_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2278_,
                            v_options_2277_,
                            v___x_2283_,
                        );
                        if v___x_2284_ == 0 {
                            leanh::lean_del_object(v___x_2273_);
                            leanh::lean_del_object(v___x_2255_);
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc_ref(v_id_2222_);
                            v___x_2285_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_id_2222_);
                            if leanh::lean_obj_tag(v___x_2285_) == 0 {
                                v_a_2286_ = leanh::lean_ctor_get(v___x_2285_, 0);
                                leanh::lean_inc(v_a_2286_);
                                leanh::lean_dec_ref_known(v___x_2285_, 1);
                                v___x_2287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10);
                                if v_isShared_2274_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_2273_, 7);
                                    leanh::lean_ctor_set(v___x_2273_, 1, v_a_2286_);
                                    leanh::lean_ctor_set(v___x_2273_, 0, v___x_2287_);
                                    v___x_2289_ = v___x_2273_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2311_ =
                                        leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2311_,
                                        0,
                                        v___x_2287_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2311_,
                                        1,
                                        v_a_2286_,
                                    );
                                    v___x_2289_ = v_reuseFailAlloc_2311_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_2273_);
                                leanh::lean_dec(v_snd_2271_);
                                leanh::lean_dec(v_fst_2270_);
                                leanh::lean_del_object(v___x_2255_);
                                leanh::lean_dec_ref(v___x_2230_);
                                leanh::lean_dec(v_a_2177_);
                                leanh::lean_dec_ref(v___x_2176_);
                                v_a_2312_ = leanh::lean_ctor_get(v___x_2285_, 0);
                                v_isSharedCheck_2319_ =
                                    (!leanh::lean_is_exclusive(v___x_2285_)) as u8;
                                if v_isSharedCheck_2319_ == 0 {
                                    v___x_2314_ = v___x_2285_;
                                    v_isShared_2315_ = v_isSharedCheck_2319_;
                                    state = 20;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2312_);
                                    leanh::lean_dec(v___x_2285_);
                                    v___x_2314_ = leanh::lean_box(0);
                                    v_isShared_2315_ = v_isSharedCheck_2319_;
                                    state = 20;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2273_);
                    leanh::lean_dec(v_snd_2271_);
                    leanh::lean_dec(v_fst_2270_);
                    leanh::lean_del_object(v___x_2255_);
                    leanh::lean_dec_ref(v___x_2230_);
                    v_a_2186_ = v___x_2275_;
                    state = 1;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc_ref(v_origType_2223_);
                leanh::lean_inc(v_userName_2221_);
                leanh::lean_inc(v_fvarId_2220_);
                v___x_2281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_2270_, v_snd_2271_, v___x_2230_, v_fvarId_2220_, v___x_2210_, v___x_2275_, v_a_2177_, v___x_2260_, v_userName_2221_, v_origType_2223_, v___x_2260_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
                v___y_2191_ = v___x_2281_;
                state = 2;
                continue;
            }
            16 => {
                v___x_2290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12);
                if v_isShared_2256_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2255_, 7);
                    leanh::lean_ctor_set(v___x_2255_, 1, v___x_2290_);
                    leanh::lean_ctor_set(v___x_2255_, 0, v___x_2289_);
                    v___x_2292_ = v___x_2255_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2310_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2290_);
                    v___x_2292_ = v_reuseFailAlloc_2310_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                leanh::lean_inc_ref(v_type_2224_);
                v___x_2293_ = l_Lean_MessageData_ofExpr(v_type_2224_);
                v___x_2294_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2294_, 0, v___x_2292_);
                leanh::lean_ctor_set(v___x_2294_, 1, v___x_2293_);
                v___x_2295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14);
                v___x_2296_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2296_, 0, v___x_2294_);
                leanh::lean_ctor_set(v___x_2296_, 1, v___x_2295_);
                leanh::lean_inc(v_snd_2271_);
                v___x_2297_ = l_Lean_MessageData_ofExpr(v_snd_2271_);
                v___x_2298_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
                v___x_2299_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v___x_2282_, v___x_2298_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
                if leanh::lean_obj_tag(v___x_2299_) == 0 {
                    v_a_2300_ = leanh::lean_ctor_get(v___x_2299_, 0);
                    leanh::lean_inc(v_a_2300_);
                    leanh::lean_dec_ref_known(v___x_2299_, 1);
                    leanh::lean_inc_ref(v_origType_2223_);
                    leanh::lean_inc(v_userName_2221_);
                    leanh::lean_inc(v_fvarId_2220_);
                    v___x_2301_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_2270_, v_snd_2271_, v___x_2230_, v_fvarId_2220_, v___x_2210_, v___x_2275_, v_a_2177_, v___x_2260_, v_userName_2221_, v_origType_2223_, v_a_2300_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
                    v___y_2191_ = v___x_2301_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2271_);
                    leanh::lean_dec(v_fst_2270_);
                    leanh::lean_dec_ref(v___x_2230_);
                    leanh::lean_dec(v_a_2177_);
                    leanh::lean_dec_ref(v___x_2176_);
                    v_a_2302_ = leanh::lean_ctor_get(v___x_2299_, 0);
                    v_isSharedCheck_2309_ = (!leanh::lean_is_exclusive(v___x_2299_)) as u8;
                    if v_isSharedCheck_2309_ == 0 {
                        v___x_2304_ = v___x_2299_;
                        v_isShared_2305_ = v_isSharedCheck_2309_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2302_);
                        leanh::lean_dec(v___x_2299_);
                        v___x_2304_ = leanh::lean_box(0);
                        v_isShared_2305_ = v_isSharedCheck_2309_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_2305_ == 0 {
                    v___x_2307_ = v___x_2304_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
                    v___x_2307_ = v_reuseFailAlloc_2308_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2307_;
            }
            20 => {
                if v_isShared_2315_ == 0 {
                    v___x_2317_ = v___x_2314_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2317_;
            }
            22 => {
                if v_isShared_2331_ == 0 {
                    v___x_2333_ = v___x_2330_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
                    v___x_2333_ = v_reuseFailAlloc_2334_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(
    mut v_upperBound_2336_: *mut leanh::LeanObject,
    mut v___x_2337_: *mut leanh::LeanObject,
    mut v___x_2338_: *mut leanh::LeanObject,
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_b_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2347_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_2336_, v___x_2337_, v___x_2338_, v_a_2339_, v_b_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
    leanh::lean_dec(v___y_2345_);
    leanh::lean_dec_ref(v___y_2344_);
    leanh::lean_dec(v___y_2343_);
    leanh::lean_dec_ref(v___y_2342_);
    leanh::lean_dec(v___y_2341_);
    leanh::lean_dec_ref(v___x_2337_);
    leanh::lean_dec(v_upperBound_2336_);
    return v_res_2347_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(
    mut v_a_2351_: *mut leanh::LeanObject,
    mut v_a_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
    mut v_a_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_2364_: u8 = 0;
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v_fst_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v_fst_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_2417_: u8 = 0;
    let mut v_mvarId_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v_usedTheorems_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v_unused_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_unused_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2455_: u8 = 0;
    let mut v_a_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2459_: u8 = 0;
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut v_reuseFailAlloc_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2469_: u8 = 0;
    let mut v_unused_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_a_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut v_reuseFailAlloc_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2368_ = lean_st_ref_take(v_a_2351_);
                v_mvarId_2369_ = leanh::lean_ctor_get(v___x_2368_, 0);
                v_entries_2370_ = leanh::lean_ctor_get(v___x_2368_, 1);
                v_ctx_2371_ = leanh::lean_ctor_get(v___x_2368_, 2);
                v_simprocs_2372_ = leanh::lean_ctor_get(v___x_2368_, 3);
                v_usedTheorems_2373_ = leanh::lean_ctor_get(v___x_2368_, 4);
                v_diag_2374_ = leanh::lean_ctor_get(v___x_2368_, 5);
                v_isSharedCheck_2481_ = (!leanh::lean_is_exclusive(v___x_2368_)) as u8;
                if v_isSharedCheck_2481_ == 0 {
                    v___x_2376_ = v___x_2368_;
                    v_isShared_2377_ = v_isSharedCheck_2481_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2374_);
                    leanh::lean_inc(v_usedTheorems_2373_);
                    leanh::lean_inc(v_simprocs_2372_);
                    leanh::lean_inc(v_ctx_2371_);
                    leanh::lean_inc(v_entries_2370_);
                    leanh::lean_inc(v_mvarId_2369_);
                    leanh::lean_dec(v___x_2368_);
                    v___x_2376_ = leanh::lean_box(0);
                    v_isShared_2377_ = v_isSharedCheck_2481_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2363_ = lean_st_ref_get(v___y_2358_);
                v_modified_2364_ = leanh::lean_ctor_get_uint8(
                    v___x_2363_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                leanh::lean_dec(v___x_2363_);
                if v_modified_2364_ == 0 {
                    v___x_2365_ = leanh::lean_box((v_modified_2364_) as usize);
                    v___x_2366_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
                    return v___x_2366_;
                } else {
                    v_a_2351_ = v___y_2358_;
                    v_a_2352_ = v___y_2359_;
                    v_a_2353_ = v___y_2360_;
                    v_a_2354_ = v___y_2361_;
                    v_a_2355_ = v___y_2362_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_2378_ = 0;
                if v_isShared_2377_ == 0 {
                    v___x_2380_ = v___x_2376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_mvarId_2369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_entries_2370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ctx_2371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_simprocs_2372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_usedTheorems_2373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 5, v_diag_2374_);
                    v___x_2380_ = v_reuseFailAlloc_2480_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2380_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_2378_,
                );
                v___x_2381_ = lean_st_ref_set(v_a_2351_, v___x_2380_);
                v___x_2382_ = lean_st_ref_get(v_a_2351_);
                v___x_2383_ = lean_st_ref_get(v_a_2351_);
                v_entries_2384_ = leanh::lean_ctor_get(v___x_2383_, 1);
                leanh::lean_inc_ref(v_entries_2384_);
                leanh::lean_dec(v___x_2383_);
                v_simprocs_2385_ = leanh::lean_ctor_get(v___x_2382_, 3);
                leanh::lean_inc_ref_n(v_simprocs_2385_, 2);
                leanh::lean_dec(v___x_2382_);
                v___x_2386_ = lean_array_get_size(v_entries_2384_);
                v___x_2387_ = leanh::lean_unsigned_to_nat(0);
                v___x_2388_ = leanh::lean_box(0);
                v___x_2389_ =
                    l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0;
                v___x_2390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_2386_, v_entries_2384_, v_simprocs_2385_, v___x_2387_, v___x_2389_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
                leanh::lean_dec_ref(v_entries_2384_);
                if leanh::lean_obj_tag(v___x_2390_) == 0 {
                    v_a_2391_ = leanh::lean_ctor_get(v___x_2390_, 0);
                    v_isSharedCheck_2471_ = (!leanh::lean_is_exclusive(v___x_2390_)) as u8;
                    if v_isSharedCheck_2471_ == 0 {
                        v___x_2393_ = v___x_2390_;
                        v_isShared_2394_ = v_isSharedCheck_2471_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2391_);
                        leanh::lean_dec(v___x_2390_);
                        v___x_2393_ = leanh::lean_box(0);
                        v_isShared_2394_ = v_isSharedCheck_2471_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_simprocs_2385_);
                    v_a_2472_ = leanh::lean_ctor_get(v___x_2390_, 0);
                    v_isSharedCheck_2479_ = (!leanh::lean_is_exclusive(v___x_2390_)) as u8;
                    if v_isSharedCheck_2479_ == 0 {
                        v___x_2474_ = v___x_2390_;
                        v_isShared_2475_ = v_isSharedCheck_2479_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2472_);
                        leanh::lean_dec(v___x_2390_);
                        v___x_2474_ = leanh::lean_box(0);
                        v_isShared_2475_ = v_isSharedCheck_2479_;
                        state = 16;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2395_ = leanh::lean_ctor_get(v_a_2391_, 0);
                v_isSharedCheck_2469_ = (!leanh::lean_is_exclusive(v_a_2391_)) as u8;
                if v_isSharedCheck_2469_ == 0 {
                    v_unused_2470_ = leanh::lean_ctor_get(v_a_2391_, 1);
                    leanh::lean_dec(v_unused_2470_);
                    v___x_2397_ = v_a_2391_;
                    v_isShared_2398_ = v_isSharedCheck_2469_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2395_);
                    leanh::lean_dec(v_a_2391_);
                    v___x_2397_ = leanh::lean_box(0);
                    v_isShared_2398_ = v_isSharedCheck_2469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_fst_2395_) == 0 {
                    leanh::lean_del_object(v___x_2393_);
                    v___x_2399_ = lean_st_ref_get(v_a_2351_);
                    v___x_2400_ = lean_st_ref_get(v_a_2351_);
                    v___x_2401_ = lean_st_ref_get(v_a_2351_);
                    v_mvarId_2402_ = leanh::lean_ctor_get(v___x_2399_, 0);
                    leanh::lean_inc(v_mvarId_2402_);
                    leanh::lean_dec(v___x_2399_);
                    v_ctx_2403_ = leanh::lean_ctor_get(v___x_2400_, 2);
                    leanh::lean_inc_ref(v_ctx_2403_);
                    leanh::lean_dec(v___x_2400_);
                    v_usedTheorems_2404_ = leanh::lean_ctor_get(v___x_2401_, 4);
                    leanh::lean_inc_ref(v_usedTheorems_2404_);
                    v_diag_2405_ = leanh::lean_ctor_get(v___x_2401_, 5);
                    leanh::lean_inc_ref(v_diag_2405_);
                    leanh::lean_dec(v___x_2401_);
                    v___x_2406_ = 1;
                    if v_isShared_2398_ == 0 {
                        leanh::lean_ctor_set(v___x_2397_, 1, v_diag_2405_);
                        leanh::lean_ctor_set(v___x_2397_, 0, v_usedTheorems_2404_);
                        v___x_2408_ = v___x_2397_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2464_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_2464_,
                            0,
                            v_usedTheorems_2404_,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_diag_2405_);
                        v___x_2408_ = v_reuseFailAlloc_2464_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2397_);
                    leanh::lean_dec_ref(v_simprocs_2385_);
                    v_val_2465_ = leanh::lean_ctor_get(v_fst_2395_, 0);
                    leanh::lean_inc(v_val_2465_);
                    leanh::lean_dec_ref_known(v_fst_2395_, 1);
                    if v_isShared_2394_ == 0 {
                        leanh::lean_ctor_set(v___x_2393_, 0, v_val_2465_);
                        v___x_2467_ = v___x_2393_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_2468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_val_2465_);
                        v___x_2467_ = v_reuseFailAlloc_2468_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc(v_mvarId_2402_);
                v___x_2409_ = l_Lean_Meta_simpTarget(
                    v_mvarId_2402_,
                    v_ctx_2403_,
                    v_simprocs_2385_,
                    v___x_2388_,
                    v___x_2406_,
                    v___x_2408_,
                    v_a_2352_,
                    v_a_2353_,
                    v_a_2354_,
                    v_a_2355_,
                );
                if leanh::lean_obj_tag(v___x_2409_) == 0 {
                    v_a_2410_ = leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2455_ = (!leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2455_ == 0 {
                        v___x_2412_ = v___x_2409_;
                        v_isShared_2413_ = v_isSharedCheck_2455_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2410_);
                        leanh::lean_dec(v___x_2409_);
                        v___x_2412_ = leanh::lean_box(0);
                        v_isShared_2413_ = v_isSharedCheck_2455_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_2402_);
                    v_a_2456_ = leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2463_ = (!leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2463_ == 0 {
                        v___x_2458_ = v___x_2409_;
                        v_isShared_2459_ = v_isSharedCheck_2463_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2456_);
                        leanh::lean_dec(v___x_2409_);
                        v___x_2458_ = leanh::lean_box(0);
                        v_isShared_2459_ = v_isSharedCheck_2463_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v_fst_2414_ = leanh::lean_ctor_get(v_a_2410_, 0);
                leanh::lean_inc(v_fst_2414_);
                v_snd_2415_ = leanh::lean_ctor_get(v_a_2410_, 1);
                leanh::lean_inc(v_snd_2415_);
                leanh::lean_dec(v_a_2410_);
                v___x_2416_ = lean_st_ref_take(v_a_2351_);
                v_modified_2417_ = leanh::lean_ctor_get_uint8(
                    v___x_2416_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_mvarId_2418_ = leanh::lean_ctor_get(v___x_2416_, 0);
                v_entries_2419_ = leanh::lean_ctor_get(v___x_2416_, 1);
                v_ctx_2420_ = leanh::lean_ctor_get(v___x_2416_, 2);
                v_simprocs_2421_ = leanh::lean_ctor_get(v___x_2416_, 3);
                v_isSharedCheck_2452_ = (!leanh::lean_is_exclusive(v___x_2416_)) as u8;
                if v_isSharedCheck_2452_ == 0 {
                    v_unused_2453_ = leanh::lean_ctor_get(v___x_2416_, 5);
                    leanh::lean_dec(v_unused_2453_);
                    v_unused_2454_ = leanh::lean_ctor_get(v___x_2416_, 4);
                    leanh::lean_dec(v_unused_2454_);
                    v___x_2423_ = v___x_2416_;
                    v_isShared_2424_ = v_isSharedCheck_2452_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_simprocs_2421_);
                    leanh::lean_inc(v_ctx_2420_);
                    leanh::lean_inc(v_entries_2419_);
                    leanh::lean_inc(v_mvarId_2418_);
                    leanh::lean_dec(v___x_2416_);
                    v___x_2423_ = leanh::lean_box(0);
                    v_isShared_2424_ = v_isSharedCheck_2452_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_usedTheorems_2425_ = leanh::lean_ctor_get(v_snd_2415_, 0);
                leanh::lean_inc_ref(v_usedTheorems_2425_);
                v_diag_2426_ = leanh::lean_ctor_get(v_snd_2415_, 1);
                leanh::lean_inc_ref(v_diag_2426_);
                leanh::lean_dec(v_snd_2415_);
                if v_isShared_2424_ == 0 {
                    leanh::lean_ctor_set(v___x_2423_, 5, v_diag_2426_);
                    leanh::lean_ctor_set(v___x_2423_, 4, v_usedTheorems_2425_);
                    v___x_2428_ = v___x_2423_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2451_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_mvarId_2418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_entries_2419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_ctx_2420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_simprocs_2421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_usedTheorems_2425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 5, v_diag_2426_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2451_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_modified_2417_,
                    );
                    v___x_2428_ = v_reuseFailAlloc_2451_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2429_ = lean_st_ref_set(v_a_2351_, v___x_2428_);
                if leanh::lean_obj_tag(v_fst_2414_) == 0 {
                    leanh::lean_dec(v_mvarId_2402_);
                    v___x_2430_ = leanh::lean_box((v___x_2406_) as usize);
                    if v_isShared_2413_ == 0 {
                        leanh::lean_ctor_set(v___x_2412_, 0, v___x_2430_);
                        v___x_2432_ = v___x_2412_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
                        v___x_2432_ = v_reuseFailAlloc_2433_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2412_);
                    v_val_2434_ = leanh::lean_ctor_get(v_fst_2414_, 0);
                    leanh::lean_inc(v_val_2434_);
                    leanh::lean_dec_ref_known(v_fst_2414_, 1);
                    v___x_2435_ = l_Lean_instBEqMVarId_beq(v_mvarId_2402_, v_val_2434_);
                    leanh::lean_dec(v_mvarId_2402_);
                    if v___x_2435_ == 0 {
                        v___x_2436_ = lean_st_ref_take(v_a_2351_);
                        v_entries_2437_ = leanh::lean_ctor_get(v___x_2436_, 1);
                        v_ctx_2438_ = leanh::lean_ctor_get(v___x_2436_, 2);
                        v_simprocs_2439_ = leanh::lean_ctor_get(v___x_2436_, 3);
                        v_usedTheorems_2440_ = leanh::lean_ctor_get(v___x_2436_, 4);
                        v_diag_2441_ = leanh::lean_ctor_get(v___x_2436_, 5);
                        v_isSharedCheck_2449_ =
                            (!leanh::lean_is_exclusive(v___x_2436_)) as u8;
                        if v_isSharedCheck_2449_ == 0 {
                            v_unused_2450_ = leanh::lean_ctor_get(v___x_2436_, 0);
                            leanh::lean_dec(v_unused_2450_);
                            v___x_2443_ = v___x_2436_;
                            v_isShared_2444_ = v_isSharedCheck_2449_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_diag_2441_);
                            leanh::lean_inc(v_usedTheorems_2440_);
                            leanh::lean_inc(v_simprocs_2439_);
                            leanh::lean_inc(v_ctx_2438_);
                            leanh::lean_inc(v_entries_2437_);
                            leanh::lean_dec(v___x_2436_);
                            v___x_2443_ = leanh::lean_box(0);
                            v_isShared_2444_ = v_isSharedCheck_2449_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_2434_);
                        v___y_2358_ = v_a_2351_;
                        v___y_2359_ = v_a_2352_;
                        v___y_2360_ = v_a_2353_;
                        v___y_2361_ = v_a_2354_;
                        v___y_2362_ = v_a_2355_;
                        state = 1;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_2432_;
            }
            11 => {
                if v_isShared_2444_ == 0 {
                    leanh::lean_ctor_set(v___x_2443_, 0, v_val_2434_);
                    v___x_2446_ = v___x_2443_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2448_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_val_2434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_entries_2437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_ctx_2438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_simprocs_2439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 4, v_usedTheorems_2440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 5, v_diag_2441_);
                    v___x_2446_ = v_reuseFailAlloc_2448_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2446_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___x_2406_,
                );
                v___x_2447_ = lean_st_ref_set(v_a_2351_, v___x_2446_);
                v___y_2358_ = v_a_2351_;
                v___y_2359_ = v_a_2352_;
                v___y_2360_ = v_a_2353_;
                v___y_2361_ = v_a_2354_;
                v___y_2362_ = v_a_2355_;
                state = 1;
                continue;
            }
            13 => {
                if v_isShared_2459_ == 0 {
                    v___x_2461_ = v___x_2458_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2462_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
                    v___x_2461_ = v_reuseFailAlloc_2462_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2461_;
            }
            15 => {
                return v___x_2467_;
            }
            16 => {
                if v_isShared_2475_ == 0 {
                    v___x_2477_ = v___x_2474_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(
    mut v_a_2482_: *mut leanh::LeanObject,
    mut v_a_2483_: *mut leanh::LeanObject,
    mut v_a_2484_: *mut leanh::LeanObject,
    mut v_a_2485_: *mut leanh::LeanObject,
    mut v_a_2486_: *mut leanh::LeanObject,
    mut v_a_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(
        v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_,
    );
    leanh::lean_dec(v_a_2486_);
    leanh::lean_dec_ref(v_a_2485_);
    leanh::lean_dec(v_a_2484_);
    leanh::lean_dec_ref(v_a_2483_);
    leanh::lean_dec(v_a_2482_);
    return v_res_2488_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(
    mut v_cls_2489_: *mut leanh::LeanObject,
    mut v_msg_2490_: *mut leanh::LeanObject,
    mut v___y_2491_: *mut leanh::LeanObject,
    mut v___y_2492_: *mut leanh::LeanObject,
    mut v___y_2493_: *mut leanh::LeanObject,
    mut v___y_2494_: *mut leanh::LeanObject,
    mut v___y_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_2489_, v_msg_2490_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
    return v___x_2497_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(
    mut v_cls_2498_: *mut leanh::LeanObject,
    mut v_msg_2499_: *mut leanh::LeanObject,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_cls_2498_, v_msg_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
    leanh::lean_dec(v___y_2504_);
    leanh::lean_dec_ref(v___y_2503_);
    leanh::lean_dec(v___y_2502_);
    leanh::lean_dec_ref(v___y_2501_);
    leanh::lean_dec(v___y_2500_);
    return v_res_2506_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(
    mut v_upperBound_2507_: *mut leanh::LeanObject,
    mut v___x_2508_: *mut leanh::LeanObject,
    mut v___x_2509_: *mut leanh::LeanObject,
    mut v_inst_2510_: *mut leanh::LeanObject,
    mut v_R_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_b_2513_: *mut leanh::LeanObject,
    mut v_c_2514_: *mut leanh::LeanObject,
    mut v___y_2515_: *mut leanh::LeanObject,
    mut v___y_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
    mut v___y_2518_: *mut leanh::LeanObject,
    mut v___y_2519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_2507_, v___x_2508_, v___x_2509_, v_a_2512_, v_b_2513_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
    return v___x_2521_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(
    mut v_upperBound_2522_: *mut leanh::LeanObject,
    mut v___x_2523_: *mut leanh::LeanObject,
    mut v___x_2524_: *mut leanh::LeanObject,
    mut v_inst_2525_: *mut leanh::LeanObject,
    mut v_R_2526_: *mut leanh::LeanObject,
    mut v_a_2527_: *mut leanh::LeanObject,
    mut v_b_2528_: *mut leanh::LeanObject,
    mut v_c_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
    mut v___y_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_upperBound_2522_, v___x_2523_, v___x_2524_, v_inst_2525_, v_R_2526_, v_a_2527_, v_b_2528_, v_c_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
    leanh::lean_dec(v___y_2534_);
    leanh::lean_dec_ref(v___y_2533_);
    leanh::lean_dec(v___y_2532_);
    leanh::lean_dec_ref(v___y_2531_);
    leanh::lean_dec(v___y_2530_);
    leanh::lean_dec_ref(v___x_2523_);
    leanh::lean_dec(v_upperBound_2522_);
    return v_res_2536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(
    mut v_as_2537_: *mut leanh::LeanObject,
    mut v_sz_2538_: usize,
    mut v_i_2539_: usize,
    mut v_b_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: usize = 0;
    let mut v___x_2545_: usize = 0;
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v_fst_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v_a_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origType_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: u8 = 0;
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2547_ = lean_usize_dec_lt(v_i_2539_, v_sz_2538_);
                if v___x_2547_ == 0 {
                    v___x_2548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2548_, 0, v_b_2540_);
                    return v___x_2548_;
                } else {
                    v_snd_2549_ = leanh::lean_ctor_get(v_b_2540_, 1);
                    v_fst_2550_ = leanh::lean_ctor_get(v_b_2540_, 0);
                    v_isSharedCheck_2587_ = (!leanh::lean_is_exclusive(v_b_2540_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2552_ = v_b_2540_;
                        v_isShared_2553_ = v_isSharedCheck_2587_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2549_);
                        leanh::lean_inc(v_fst_2550_);
                        leanh::lean_dec(v_b_2540_);
                        v___x_2552_ = leanh::lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2587_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2544_ = 1usize;
                v___x_2545_ = lean_usize_add(v_i_2539_, v___x_2544_);
                v_i_2539_ = v___x_2545_;
                v_b_2540_ = v_a_2543_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_2554_ = leanh::lean_ctor_get(v_snd_2549_, 0);
                v_snd_2555_ = leanh::lean_ctor_get(v_snd_2549_, 1);
                v_isSharedCheck_2586_ = (!leanh::lean_is_exclusive(v_snd_2549_)) as u8;
                if v_isSharedCheck_2586_ == 0 {
                    v___x_2557_ = v_snd_2549_;
                    v_isShared_2558_ = v_isSharedCheck_2586_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2555_);
                    leanh::lean_inc(v_fst_2554_);
                    leanh::lean_dec(v_snd_2549_);
                    v___x_2557_ = leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2586_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_2559_ = lean_array_uget_borrowed(v_as_2537_, v_i_2539_);
                v_fvarId_2560_ = leanh::lean_ctor_get(v_a_2559_, 0);
                v_userName_2561_ = leanh::lean_ctor_get(v_a_2559_, 1);
                v_origType_2562_ = leanh::lean_ctor_get(v_a_2559_, 3);
                v_type_2563_ = leanh::lean_ctor_get(v_a_2559_, 4);
                v_proof_2564_ = leanh::lean_ctor_get(v_a_2559_, 5);
                leanh::lean_inc_ref(v_type_2563_);
                v___x_2578_ = l_Lean_Expr_isTrue(v_type_2563_);
                if v___x_2578_ == 0 {
                    v___x_2579_ = (leanh::lean_unbox(v_snd_2555_) as u8);
                    if v___x_2579_ == 0 {
                        v___x_2580_ = lean_expr_eqv(v_type_2563_, v_origType_2562_);
                        if v___x_2580_ == 0 {
                            leanh::lean_dec(v_snd_2555_);
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_2557_);
                            leanh::lean_del_object(v___x_2552_);
                            v___x_2581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2581_, 0, v_fst_2554_);
                            leanh::lean_ctor_set(v___x_2581_, 1, v_snd_2555_);
                            v___x_2582_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2582_, 0, v_fst_2550_);
                            leanh::lean_ctor_set(v___x_2582_, 1, v___x_2581_);
                            v_a_2543_ = v___x_2582_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_2555_);
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2557_);
                    leanh::lean_del_object(v___x_2552_);
                    leanh::lean_inc(v_fvarId_2560_);
                    v___x_2583_ = lean_array_push(v_fst_2554_, v_fvarId_2560_);
                    v___x_2584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2584_, 0, v___x_2583_);
                    leanh::lean_ctor_set(v___x_2584_, 1, v_snd_2555_);
                    v___x_2585_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2585_, 0, v_fst_2550_);
                    leanh::lean_ctor_set(v___x_2585_, 1, v___x_2584_);
                    v_a_2543_ = v___x_2585_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_fvarId_2560_);
                v___x_2566_ = lean_array_push(v_fst_2554_, v_fvarId_2560_);
                v___x_2567_ = 0;
                v___x_2568_ = 0;
                leanh::lean_inc_ref(v_proof_2564_);
                leanh::lean_inc_ref(v_type_2563_);
                leanh::lean_inc(v_userName_2561_);
                v___x_2569_ = leanh::lean_alloc_ctor(0, 3, (2) as u32);
                leanh::lean_ctor_set(v___x_2569_, 0, v_userName_2561_);
                leanh::lean_ctor_set(v___x_2569_, 1, v_type_2563_);
                leanh::lean_ctor_set(v___x_2569_, 2, v_proof_2564_);
                leanh::lean_ctor_set_uint8(
                    v___x_2569_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2567_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2569_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_2568_,
                );
                v___x_2570_ = lean_array_push(v_fst_2550_, v___x_2569_);
                v___x_2571_ = leanh::lean_box((v___x_2547_) as usize);
                if v_isShared_2558_ == 0 {
                    leanh::lean_ctor_set(v___x_2557_, 1, v___x_2571_);
                    leanh::lean_ctor_set(v___x_2557_, 0, v___x_2566_);
                    v___x_2573_ = v___x_2557_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2571_);
                    v___x_2573_ = v_reuseFailAlloc_2577_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2553_ == 0 {
                    leanh::lean_ctor_set(v___x_2552_, 1, v___x_2573_);
                    leanh::lean_ctor_set(v___x_2552_, 0, v___x_2570_);
                    v___x_2575_ = v___x_2552_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2576_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2573_);
                    v___x_2575_ = v_reuseFailAlloc_2576_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2543_ = v___x_2575_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(
    mut v_as_2588_: *mut leanh::LeanObject,
    mut v_sz_2589_: *mut leanh::LeanObject,
    mut v_i_2590_: *mut leanh::LeanObject,
    mut v_b_2591_: *mut leanh::LeanObject,
    mut v___y_2592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2593_: usize = 0;
    let mut v_i_boxed_2594_: usize = 0;
    let mut v_res_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2593_ = leanh::lean_unbox_usize(v_sz_2589_);
    leanh::lean_dec(v_sz_2589_);
    v_i_boxed_2594_ = leanh::lean_unbox_usize(v_i_2590_);
    leanh::lean_dec(v_i_2590_);
    v_res_2595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_2588_, v_sz_boxed_2593_, v_i_boxed_2594_, v_b_2591_);
    leanh::lean_dec_ref(v_as_2588_);
    return v_res_2595_;
}
pub unsafe fn l_Lean_Meta_SimpAll_main(
    mut v_a_2598_: *mut leanh::LeanObject,
    mut v_a_2599_: *mut leanh::LeanObject,
    mut v_a_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: u8 = 0;
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2617_: usize = 0;
    let mut v___x_2618_: usize = 0;
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v_a_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_a_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut v_a_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut v_a_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2670_: u8 = 0;
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_a_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2678_: u8 = 0;
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2604_ =
                    l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(
                        v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_,
                    );
                if leanh::lean_obj_tag(v___x_2604_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2604_, 1);
                    v___x_2605_ =
                        l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(
                            v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_,
                        );
                    if leanh::lean_obj_tag(v___x_2605_) == 0 {
                        v_a_2606_ = leanh::lean_ctor_get(v___x_2605_, 0);
                        v_isSharedCheck_2666_ =
                            (!leanh::lean_is_exclusive(v___x_2605_)) as u8;
                        if v_isSharedCheck_2666_ == 0 {
                            v___x_2608_ = v___x_2605_;
                            v_isShared_2609_ = v_isSharedCheck_2666_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2606_);
                            leanh::lean_dec(v___x_2605_);
                            v___x_2608_ = leanh::lean_box(0);
                            v_isShared_2609_ = v_isSharedCheck_2666_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2667_ = leanh::lean_ctor_get(v___x_2605_, 0);
                        v_isSharedCheck_2674_ =
                            (!leanh::lean_is_exclusive(v___x_2605_)) as u8;
                        if v_isSharedCheck_2674_ == 0 {
                            v___x_2669_ = v___x_2605_;
                            v_isShared_2670_ = v_isSharedCheck_2674_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2667_);
                            leanh::lean_dec(v___x_2605_);
                            v___x_2669_ = leanh::lean_box(0);
                            v_isShared_2670_ = v_isSharedCheck_2674_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v_a_2675_ = leanh::lean_ctor_get(v___x_2604_, 0);
                    v_isSharedCheck_2682_ = (!leanh::lean_is_exclusive(v___x_2604_)) as u8;
                    if v_isSharedCheck_2682_ == 0 {
                        v___x_2677_ = v___x_2604_;
                        v_isShared_2678_ = v_isSharedCheck_2682_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2675_);
                        leanh::lean_dec(v___x_2604_);
                        v___x_2677_ = leanh::lean_box(0);
                        v_isShared_2678_ = v_isSharedCheck_2682_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2610_ = (leanh::lean_unbox(v_a_2606_) as u8);
                if v___x_2610_ == 0 {
                    leanh::lean_del_object(v___x_2608_);
                    v___x_2611_ = lean_st_ref_get(v_a_2598_);
                    v___x_2612_ = lean_st_ref_get(v_a_2598_);
                    v_entries_2613_ = leanh::lean_ctor_get(v___x_2612_, 1);
                    leanh::lean_inc_ref(v_entries_2613_);
                    leanh::lean_dec(v___x_2612_);
                    v___x_2614_ = l_Lean_Meta_SimpAll_main___closed__0;
                    v___x_2615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2615_, 0, v___x_2614_);
                    leanh::lean_ctor_set(v___x_2615_, 1, v_a_2606_);
                    v___x_2616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2616_, 0, v___x_2614_);
                    leanh::lean_ctor_set(v___x_2616_, 1, v___x_2615_);
                    v_sz_2617_ = lean_array_size(v_entries_2613_);
                    v___x_2618_ = 0usize;
                    v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_2613_, v_sz_2617_, v___x_2618_, v___x_2616_);
                    leanh::lean_dec_ref(v_entries_2613_);
                    if leanh::lean_obj_tag(v___x_2619_) == 0 {
                        v_a_2620_ = leanh::lean_ctor_get(v___x_2619_, 0);
                        leanh::lean_inc(v_a_2620_);
                        leanh::lean_dec_ref_known(v___x_2619_, 1);
                        v_mvarId_2621_ = leanh::lean_ctor_get(v___x_2611_, 0);
                        leanh::lean_inc(v_mvarId_2621_);
                        leanh::lean_dec(v___x_2611_);
                        v_fst_2622_ = leanh::lean_ctor_get(v_a_2620_, 0);
                        leanh::lean_inc(v_fst_2622_);
                        v_snd_2623_ = leanh::lean_ctor_get(v_a_2620_, 1);
                        leanh::lean_inc(v_snd_2623_);
                        leanh::lean_dec(v_a_2620_);
                        v___x_2624_ = l_Lean_MVarId_assertHypotheses(
                            v_mvarId_2621_,
                            v_fst_2622_,
                            v_a_2599_,
                            v_a_2600_,
                            v_a_2601_,
                            v_a_2602_,
                        );
                        if leanh::lean_obj_tag(v___x_2624_) == 0 {
                            v_a_2625_ = leanh::lean_ctor_get(v___x_2624_, 0);
                            leanh::lean_inc(v_a_2625_);
                            leanh::lean_dec_ref_known(v___x_2624_, 1);
                            v_snd_2626_ = leanh::lean_ctor_get(v_a_2625_, 1);
                            leanh::lean_inc(v_snd_2626_);
                            leanh::lean_dec(v_a_2625_);
                            v_fst_2627_ = leanh::lean_ctor_get(v_snd_2623_, 0);
                            leanh::lean_inc(v_fst_2627_);
                            leanh::lean_dec(v_snd_2623_);
                            v___x_2628_ = l_Lean_MVarId_tryClearMany(
                                v_snd_2626_,
                                v_fst_2627_,
                                v_a_2599_,
                                v_a_2600_,
                                v_a_2601_,
                                v_a_2602_,
                            );
                            leanh::lean_dec(v_fst_2627_);
                            if leanh::lean_obj_tag(v___x_2628_) == 0 {
                                v_a_2629_ = leanh::lean_ctor_get(v___x_2628_, 0);
                                v_isSharedCheck_2637_ =
                                    (!leanh::lean_is_exclusive(v___x_2628_)) as u8;
                                if v_isSharedCheck_2637_ == 0 {
                                    v___x_2631_ = v___x_2628_;
                                    v_isShared_2632_ = v_isSharedCheck_2637_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2629_);
                                    leanh::lean_dec(v___x_2628_);
                                    v___x_2631_ = leanh::lean_box(0);
                                    v_isShared_2632_ = v_isSharedCheck_2637_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_2638_ = leanh::lean_ctor_get(v___x_2628_, 0);
                                v_isSharedCheck_2645_ =
                                    (!leanh::lean_is_exclusive(v___x_2628_)) as u8;
                                if v_isSharedCheck_2645_ == 0 {
                                    v___x_2640_ = v___x_2628_;
                                    v_isShared_2641_ = v_isSharedCheck_2645_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2638_);
                                    leanh::lean_dec(v___x_2628_);
                                    v___x_2640_ = leanh::lean_box(0);
                                    v_isShared_2641_ = v_isSharedCheck_2645_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_snd_2623_);
                            v_a_2646_ = leanh::lean_ctor_get(v___x_2624_, 0);
                            v_isSharedCheck_2653_ =
                                (!leanh::lean_is_exclusive(v___x_2624_)) as u8;
                            if v_isSharedCheck_2653_ == 0 {
                                v___x_2648_ = v___x_2624_;
                                v_isShared_2649_ = v_isSharedCheck_2653_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2646_);
                                leanh::lean_dec(v___x_2624_);
                                v___x_2648_ = leanh::lean_box(0);
                                v_isShared_2649_ = v_isSharedCheck_2653_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2611_);
                        v_a_2654_ = leanh::lean_ctor_get(v___x_2619_, 0);
                        v_isSharedCheck_2661_ =
                            (!leanh::lean_is_exclusive(v___x_2619_)) as u8;
                        if v_isSharedCheck_2661_ == 0 {
                            v___x_2656_ = v___x_2619_;
                            v_isShared_2657_ = v_isSharedCheck_2661_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2654_);
                            leanh::lean_dec(v___x_2619_);
                            v___x_2656_ = leanh::lean_box(0);
                            v_isShared_2657_ = v_isSharedCheck_2661_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2606_);
                    v___x_2662_ = leanh::lean_box(0);
                    if v_isShared_2609_ == 0 {
                        leanh::lean_ctor_set(v___x_2608_, 0, v___x_2662_);
                        v___x_2664_ = v___x_2608_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2665_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
                        v___x_2664_ = v_reuseFailAlloc_2665_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2633_, 0, v_a_2629_);
                if v_isShared_2632_ == 0 {
                    leanh::lean_ctor_set(v___x_2631_, 0, v___x_2633_);
                    v___x_2635_ = v___x_2631_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
                    v___x_2635_ = v_reuseFailAlloc_2636_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2635_;
            }
            4 => {
                if v_isShared_2641_ == 0 {
                    v___x_2643_ = v___x_2640_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2644_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
                    v___x_2643_ = v_reuseFailAlloc_2644_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2643_;
            }
            6 => {
                if v_isShared_2649_ == 0 {
                    v___x_2651_ = v___x_2648_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
                    v___x_2651_ = v_reuseFailAlloc_2652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2651_;
            }
            8 => {
                if v_isShared_2657_ == 0 {
                    v___x_2659_ = v___x_2656_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2659_;
            }
            10 => {
                return v___x_2664_;
            }
            11 => {
                if v_isShared_2670_ == 0 {
                    v___x_2672_ = v___x_2669_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
                    v___x_2672_ = v_reuseFailAlloc_2673_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2672_;
            }
            13 => {
                if v_isShared_2678_ == 0 {
                    v___x_2680_ = v___x_2677_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
                    v___x_2680_ = v_reuseFailAlloc_2681_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SimpAll_main___boxed(
    mut v_a_2683_: *mut leanh::LeanObject,
    mut v_a_2684_: *mut leanh::LeanObject,
    mut v_a_2685_: *mut leanh::LeanObject,
    mut v_a_2686_: *mut leanh::LeanObject,
    mut v_a_2687_: *mut leanh::LeanObject,
    mut v_a_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Lean_Meta_SimpAll_main(v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
    leanh::lean_dec(v_a_2687_);
    leanh::lean_dec_ref(v_a_2686_);
    leanh::lean_dec(v_a_2685_);
    leanh::lean_dec_ref(v_a_2684_);
    leanh::lean_dec(v_a_2683_);
    return v_res_2689_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(
    mut v_as_2690_: *mut leanh::LeanObject,
    mut v_sz_2691_: usize,
    mut v_i_2692_: usize,
    mut v_b_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
    mut v___y_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_2690_, v_sz_2691_, v_i_2692_, v_b_2693_);
    return v___x_2700_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(
    mut v_as_2701_: *mut leanh::LeanObject,
    mut v_sz_2702_: *mut leanh::LeanObject,
    mut v_i_2703_: *mut leanh::LeanObject,
    mut v_b_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
    mut v___y_2708_: *mut leanh::LeanObject,
    mut v___y_2709_: *mut leanh::LeanObject,
    mut v___y_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2711_: usize = 0;
    let mut v_i_boxed_2712_: usize = 0;
    let mut v_res_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2711_ = leanh::lean_unbox_usize(v_sz_2702_);
    leanh::lean_dec(v_sz_2702_);
    v_i_boxed_2712_ = leanh::lean_unbox_usize(v_i_2703_);
    leanh::lean_dec(v_i_2703_);
    v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_2701_, v_sz_boxed_2711_, v_i_boxed_2712_, v_b_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    leanh::lean_dec(v___y_2709_);
    leanh::lean_dec_ref(v___y_2708_);
    leanh::lean_dec(v___y_2707_);
    leanh::lean_dec_ref(v___y_2706_);
    leanh::lean_dec(v___y_2705_);
    leanh::lean_dec_ref(v_as_2701_);
    return v_res_2713_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(
    mut v_mvarId_2714_: *mut leanh::LeanObject,
    mut v_x_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_a_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_2714_,
                    v_x_2715_,
                    v___y_2716_,
                    v___y_2717_,
                    v___y_2718_,
                    v___y_2719_,
                );
                if leanh::lean_obj_tag(v___x_2721_) == 0 {
                    v_a_2722_ = leanh::lean_ctor_get(v___x_2721_, 0);
                    v_isSharedCheck_2729_ = (!leanh::lean_is_exclusive(v___x_2721_)) as u8;
                    if v_isSharedCheck_2729_ == 0 {
                        v___x_2724_ = v___x_2721_;
                        v_isShared_2725_ = v_isSharedCheck_2729_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2722_);
                        leanh::lean_dec(v___x_2721_);
                        v___x_2724_ = leanh::lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2729_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2730_ = leanh::lean_ctor_get(v___x_2721_, 0);
                    v_isSharedCheck_2737_ = (!leanh::lean_is_exclusive(v___x_2721_)) as u8;
                    if v_isSharedCheck_2737_ == 0 {
                        v___x_2732_ = v___x_2721_;
                        v_isShared_2733_ = v_isSharedCheck_2737_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2730_);
                        leanh::lean_dec(v___x_2721_);
                        v___x_2732_ = leanh::lean_box(0);
                        v_isShared_2733_ = v_isSharedCheck_2737_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2725_ == 0 {
                    v___x_2727_ = v___x_2724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
                    v___x_2727_ = v_reuseFailAlloc_2728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2727_;
            }
            3 => {
                if v_isShared_2733_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(
    mut v_mvarId_2738_: *mut leanh::LeanObject,
    mut v_x_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
    mut v___y_2741_: *mut leanh::LeanObject,
    mut v___y_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(
        v_mvarId_2738_,
        v_x_2739_,
        v___y_2740_,
        v___y_2741_,
        v___y_2742_,
        v___y_2743_,
    );
    leanh::lean_dec(v___y_2743_);
    leanh::lean_dec_ref(v___y_2742_);
    leanh::lean_dec(v___y_2741_);
    leanh::lean_dec_ref(v___y_2740_);
    return v_res_2745_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(
    mut v_00_u03b1_2746_: *mut leanh::LeanObject,
    mut v_mvarId_2747_: *mut leanh::LeanObject,
    mut v_x_2748_: *mut leanh::LeanObject,
    mut v___y_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
    mut v___y_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(
        v_mvarId_2747_,
        v_x_2748_,
        v___y_2749_,
        v___y_2750_,
        v___y_2751_,
        v___y_2752_,
    );
    return v___x_2754_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(
    mut v_00_u03b1_2755_: *mut leanh::LeanObject,
    mut v_mvarId_2756_: *mut leanh::LeanObject,
    mut v_x_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
    mut v___y_2760_: *mut leanh::LeanObject,
    mut v___y_2761_: *mut leanh::LeanObject,
    mut v___y_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2763_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(
        v_00_u03b1_2755_,
        v_mvarId_2756_,
        v_x_2757_,
        v___y_2758_,
        v___y_2759_,
        v___y_2760_,
        v___y_2761_,
    );
    leanh::lean_dec(v___y_2761_);
    leanh::lean_dec_ref(v___y_2760_);
    leanh::lean_dec(v___y_2759_);
    leanh::lean_dec_ref(v___y_2758_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(
    mut v_msg_2764_: *mut leanh::LeanObject,
    mut v___y_2765_: *mut leanh::LeanObject,
    mut v___y_2766_: *mut leanh::LeanObject,
    mut v___y_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2770_ = leanh::lean_ctor_get(v___y_2767_, 5);
                v___x_2771_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
                v_a_2772_ = leanh::lean_ctor_get(v___x_2771_, 0);
                v_isSharedCheck_2780_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                if v_isSharedCheck_2780_ == 0 {
                    v___x_2774_ = v___x_2771_;
                    v_isShared_2775_ = v_isSharedCheck_2780_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2772_);
                    leanh::lean_dec(v___x_2771_);
                    v___x_2774_ = leanh::lean_box(0);
                    v_isShared_2775_ = v_isSharedCheck_2780_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2770_);
                v___x_2776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2776_, 0, v_ref_2770_);
                leanh::lean_ctor_set(v___x_2776_, 1, v_a_2772_);
                if v_isShared_2775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2774_, 1);
                    leanh::lean_ctor_set(v___x_2774_, 0, v___x_2776_);
                    v___x_2778_ = v___x_2774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2779_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
                    v___x_2778_ = v_reuseFailAlloc_2779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(
    mut v_msg_2781_: *mut leanh::LeanObject,
    mut v___y_2782_: *mut leanh::LeanObject,
    mut v___y_2783_: *mut leanh::LeanObject,
    mut v___y_2784_: *mut leanh::LeanObject,
    mut v___y_2785_: *mut leanh::LeanObject,
    mut v___y_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(
        v_msg_2781_,
        v___y_2782_,
        v___y_2783_,
        v___y_2784_,
        v___y_2785_,
    );
    leanh::lean_dec(v___y_2785_);
    leanh::lean_dec_ref(v___y_2784_);
    leanh::lean_dec(v___y_2783_);
    leanh::lean_dec_ref(v___y_2782_);
    return v_res_2787_;
}
pub unsafe fn _init_l_Lean_Meta_simpAll___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2789_ = l_Lean_Meta_simpAll___lam__0___closed__0;
    v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
    return v___x_2790_;
}
pub unsafe fn l_Lean_Meta_simpAll___lam__0(
    mut v___x_2791_: *mut leanh::LeanObject,
    mut v_ctx_2792_: *mut leanh::LeanObject,
    mut v_mvarId_2793_: *mut leanh::LeanObject,
    mut v___y_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_failIfUnchanged_2815_: u8 = 0;
    let mut v_val_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2823_: u8 = 0;
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2827_: u8 = 0;
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2799_ = lean_st_mk_ref(v___x_2791_);
                v___x_2800_ = l_Lean_Meta_SimpAll_main(
                    v___x_2799_,
                    v___y_2794_,
                    v___y_2795_,
                    v___y_2796_,
                    v___y_2797_,
                );
                if leanh::lean_obj_tag(v___x_2800_) == 0 {
                    v_a_2801_ = leanh::lean_ctor_get(v___x_2800_, 0);
                    v_isSharedCheck_2828_ = (!leanh::lean_is_exclusive(v___x_2800_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2803_ = v___x_2800_;
                        v_isShared_2804_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2801_);
                        leanh::lean_dec(v___x_2800_);
                        v___x_2803_ = leanh::lean_box(0);
                        v_isShared_2804_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2799_);
                    v_a_2829_ = leanh::lean_ctor_get(v___x_2800_, 0);
                    v_isSharedCheck_2836_ = (!leanh::lean_is_exclusive(v___x_2800_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2800_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2829_);
                        leanh::lean_dec(v___x_2800_);
                        v___x_2831_ = leanh::lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2805_ = lean_st_ref_get(v___x_2799_);
                leanh::lean_dec(v___x_2799_);
                if leanh::lean_obj_tag(v_a_2801_) == 1 {
                    v_config_2814_ = leanh::lean_ctor_get(v_ctx_2792_, 0);
                    v_failIfUnchanged_2815_ = leanh::lean_ctor_get_uint8(
                        v_config_2814_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 13) as u32,
                    );
                    if v_failIfUnchanged_2815_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v_val_2816_ = leanh::lean_ctor_get(v_a_2801_, 0);
                        v___x_2817_ = l_Lean_instBEqMVarId_beq(v_mvarId_2793_, v_val_2816_);
                        if v___x_2817_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_2801_, 1);
                            leanh::lean_dec(v___x_2805_);
                            leanh::lean_del_object(v___x_2803_);
                            v___x_2818_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_simpAll___lam__0___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_simpAll___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_simpAll___lam__0___closed__1,
                            );
                            v___x_2819_ =
                                l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(
                                    v___x_2818_,
                                    v___y_2794_,
                                    v___y_2795_,
                                    v___y_2796_,
                                    v___y_2797_,
                                );
                            v_a_2820_ = leanh::lean_ctor_get(v___x_2819_, 0);
                            v_isSharedCheck_2827_ =
                                (!leanh::lean_is_exclusive(v___x_2819_)) as u8;
                            if v_isSharedCheck_2827_ == 0 {
                                v___x_2822_ = v___x_2819_;
                                v_isShared_2823_ = v_isSharedCheck_2827_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2820_);
                                leanh::lean_dec(v___x_2819_);
                                v___x_2822_ = leanh::lean_box(0);
                                v_isShared_2823_ = v_isSharedCheck_2827_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_usedTheorems_2807_ = leanh::lean_ctor_get(v___x_2805_, 4);
                leanh::lean_inc_ref(v_usedTheorems_2807_);
                v_diag_2808_ = leanh::lean_ctor_get(v___x_2805_, 5);
                leanh::lean_inc_ref(v_diag_2808_);
                leanh::lean_dec(v___x_2805_);
                v___x_2809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2809_, 0, v_usedTheorems_2807_);
                leanh::lean_ctor_set(v___x_2809_, 1, v_diag_2808_);
                v___x_2810_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2810_, 0, v_a_2801_);
                leanh::lean_ctor_set(v___x_2810_, 1, v___x_2809_);
                if v_isShared_2804_ == 0 {
                    leanh::lean_ctor_set(v___x_2803_, 0, v___x_2810_);
                    v___x_2812_ = v___x_2803_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2812_;
            }
            4 => {
                if v_isShared_2823_ == 0 {
                    v___x_2825_ = v___x_2822_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
                    v___x_2825_ = v_reuseFailAlloc_2826_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2825_;
            }
            6 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_simpAll___lam__0___boxed(
    mut v___x_2837_: *mut leanh::LeanObject,
    mut v_ctx_2838_: *mut leanh::LeanObject,
    mut v_mvarId_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2845_ = l_Lean_Meta_simpAll___lam__0(
        v___x_2837_,
        v_ctx_2838_,
        v_mvarId_2839_,
        v___y_2840_,
        v___y_2841_,
        v___y_2842_,
        v___y_2843_,
    );
    leanh::lean_dec(v___y_2843_);
    leanh::lean_dec_ref(v___y_2842_);
    leanh::lean_dec(v___y_2841_);
    leanh::lean_dec_ref(v___y_2840_);
    leanh::lean_dec(v_mvarId_2839_);
    leanh::lean_dec_ref(v_ctx_2838_);
    return v_res_2845_;
}
pub unsafe fn l_Lean_Meta_simpAll(
    mut v_mvarId_2848_: *mut leanh::LeanObject,
    mut v_ctx_2849_: *mut leanh::LeanObject,
    mut v_simprocs_2850_: *mut leanh::LeanObject,
    mut v_stats_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedTheorems_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedTheorems_2857_ = leanh::lean_ctor_get(v_stats_2851_, 0);
    v_diag_2858_ = leanh::lean_ctor_get(v_stats_2851_, 1);
    v___x_2859_ = 0;
    v___x_2860_ = l_Lean_Meta_simpAll___closed__0;
    leanh::lean_inc_ref(v_diag_2858_);
    leanh::lean_inc_ref(v_usedTheorems_2857_);
    leanh::lean_inc_ref(v_ctx_2849_);
    leanh::lean_inc_n(v_mvarId_2848_, 2);
    v___x_2861_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
    leanh::lean_ctor_set(v___x_2861_, 0, v_mvarId_2848_);
    leanh::lean_ctor_set(v___x_2861_, 1, v___x_2860_);
    leanh::lean_ctor_set(v___x_2861_, 2, v_ctx_2849_);
    leanh::lean_ctor_set(v___x_2861_, 3, v_simprocs_2850_);
    leanh::lean_ctor_set(v___x_2861_, 4, v_usedTheorems_2857_);
    leanh::lean_ctor_set(v___x_2861_, 5, v_diag_2858_);
    leanh::lean_ctor_set_uint8(
        v___x_2861_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
        v___x_2859_,
    );
    v___f_2862_ = leanh::lean_alloc_closure(
        l_Lean_Meta_simpAll___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_2862_, 0, v___x_2861_);
    leanh::lean_closure_set(v___f_2862_, 1, v_ctx_2849_);
    leanh::lean_closure_set(v___f_2862_, 2, v_mvarId_2848_);
    v___x_2863_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(
        v_mvarId_2848_,
        v___f_2862_,
        v_a_2852_,
        v_a_2853_,
        v_a_2854_,
        v_a_2855_,
    );
    return v___x_2863_;
}
pub unsafe fn l_Lean_Meta_simpAll___boxed(
    mut v_mvarId_2864_: *mut leanh::LeanObject,
    mut v_ctx_2865_: *mut leanh::LeanObject,
    mut v_simprocs_2866_: *mut leanh::LeanObject,
    mut v_stats_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
    mut v_a_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2873_ = l_Lean_Meta_simpAll(
        v_mvarId_2864_,
        v_ctx_2865_,
        v_simprocs_2866_,
        v_stats_2867_,
        v_a_2868_,
        v_a_2869_,
        v_a_2870_,
        v_a_2871_,
    );
    leanh::lean_dec(v_a_2871_);
    leanh::lean_dec_ref(v_a_2870_);
    leanh::lean_dec(v_a_2869_);
    leanh::lean_dec_ref(v_a_2868_);
    leanh::lean_dec_ref(v_stats_2867_);
    return v_res_2873_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(
    mut v_00_u03b1_2874_: *mut leanh::LeanObject,
    mut v_msg_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(
        v_msg_2875_,
        v___y_2876_,
        v___y_2877_,
        v___y_2878_,
        v___y_2879_,
    );
    return v___x_2881_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(
    mut v_00_u03b1_2882_: *mut leanh::LeanObject,
    mut v_msg_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(
        v_00_u03b1_2882_,
        v_msg_2883_,
        v___y_2884_,
        v___y_2885_,
        v___y_2886_,
        v___y_2887_,
    );
    leanh::lean_dec(v___y_2887_);
    leanh::lean_dec_ref(v___y_2886_);
    leanh::lean_dec(v___y_2885_);
    leanh::lean_dec_ref(v___y_2884_);
    return v_res_2889_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5;
    v___x_2960_ = 0;
    v___x_2961_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_;
    v___x_2962_ = l_Lean_registerTraceClass(v___x_2959_, v___x_2960_, v___x_2961_);
    return v___x_2962_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2____boxed(
    mut v_a_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2964_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
    return v_res_2964_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_SimpAll_instInhabitedEntry_default =
        _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default();
    leanh::lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry_default);
    l_Lean_Meta_SimpAll_instInhabitedEntry = _init_l_Lean_Meta_SimpAll_instInhabitedEntry();
    leanh::lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry);
    res = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_SimpAll(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_SimpAll(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
}