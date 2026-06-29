// Lean compiler output
// Module: Lean.Elab.PreDefinition.MkInhabitant
// Imports: Lean.Meta.AppBuilder Lean.PrettyPrinter Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_infer_type, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_st_ref_get,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_isForall, l_Lean_mkAppB,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkDefault, l_Lean_Meta_mkOfNonempty,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::WHNF::{l_Lean_Meta_unfoldDefinition_x3f, l_Lean_Meta_whnfCore};
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, runtime_initialize_Lean_PrettyPrinter,
};
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13340093926952294564 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13340093926952294564 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value) as *mut crate::leanh::LeanObject,17998702798483655788 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value) as *mut crate::leanh::LeanObject,6605161548626312362 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    32,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        44, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 112, 114, 111, 118, 101, 32, 116,
        104, 97, 116, 32, 116, 104, 101, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value: crate::leanh::LeanStringObject<
    137,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 137,
    m_capacity: 137,
    m_length: 136,
    m_data: [
        10, 105, 115, 32, 110, 111, 110, 101, 109, 112, 116, 121, 46, 10, 10, 84, 104, 105, 115,
        32, 112, 114, 111, 99, 101, 115, 115, 32, 117, 115, 101, 115, 32, 109, 117, 108, 116, 105,
        112, 108, 101, 32, 115, 116, 114, 97, 116, 101, 103, 105, 101, 115, 58, 10, 45, 32, 73,
        116, 32, 108, 111, 111, 107, 115, 32, 102, 111, 114, 32, 97, 32, 112, 97, 114, 97, 109,
        101, 116, 101, 114, 32, 116, 104, 97, 116, 32, 109, 97, 116, 99, 104, 101, 115, 32, 116,
        104, 101, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 46, 10, 45, 32, 73,
        116, 32, 116, 114, 105, 101, 115, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 105,
        110, 103, 32, 39, 0,
    ],
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [39, 32, 97, 110, 100, 32, 39, 0],
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0],
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value)
                as *mut crate::leanh::LeanObject,
            13229434762204987278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value: crate::leanh::LeanStringObject<
    77,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 77,
    m_capacity: 77,
    m_length: 76,
    m_data: [
        39, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 102, 111, 114, 32, 116, 104, 101,
        32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 44, 32, 119, 104, 105, 108, 101,
        32, 109, 97, 107, 105, 110, 103, 32, 101, 118, 101, 114, 121, 32, 112, 97, 114, 97, 109,
        101, 116, 101, 114, 32, 105, 110, 116, 111, 32, 97, 32, 108, 111, 99, 97, 108, 32, 39, 0,
    ],
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value: crate::leanh::LeanStringObject<
    182,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 182,
    m_capacity: 182,
    m_length: 181,
    m_data: [
        39, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 10, 45, 32, 73, 116, 32, 116, 114, 105,
        101, 115, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 116, 104, 101, 32, 114, 101,
        116, 117, 114, 110, 32, 116, 121, 112, 101, 46, 10, 10, 73, 102, 32, 116, 104, 101, 32,
        114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 32, 105, 115, 32, 100, 101, 102, 105,
        110, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 39, 115, 116, 114, 117,
        99, 116, 117, 114, 101, 39, 32, 111, 114, 32, 39, 105, 110, 100, 117, 99, 116, 105, 118,
        101, 39, 32, 99, 111, 109, 109, 97, 110, 100, 44, 32, 121, 111, 117, 32, 99, 97, 110, 32,
        116, 114, 121, 32, 97, 100, 100, 105, 110, 103, 32, 97, 32, 39, 100, 101, 114, 105, 118,
        105, 110, 103, 32, 78, 111, 110, 101, 109, 112, 116, 121, 39, 32, 99, 108, 97, 117, 115,
        101, 32, 116, 111, 32, 105, 116, 46, 0,
    ],
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(
    mut v_k_733_: *mut crate::leanh::LeanObject,
    mut v_b_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_738_);
    crate::leanh::lean_inc_ref(v___y_737_);
    crate::leanh::lean_inc(v___y_736_);
    crate::leanh::lean_inc_ref(v___y_735_);
    v___x_740_ = crate::leanh::lean_apply_6(
        v_k_733_,
        v_b_734_,
        v___y_735_,
        v___y_736_,
        v___y_737_,
        v___y_738_,
        crate::leanh::lean_box(0),
    );
    return v___x_740_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(
    mut v_k_741_: *mut crate::leanh::LeanObject,
    mut v_b_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_741_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
    crate::leanh::lean_dec(v___y_746_);
    crate::leanh::lean_dec_ref(v___y_745_);
    crate::leanh::lean_dec(v___y_744_);
    crate::leanh::lean_dec_ref(v___y_743_);
    return v_res_748_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(
    mut v_name_749_: *mut crate::leanh::LeanObject,
    mut v_type_750_: *mut crate::leanh::LeanObject,
    mut v_val_751_: *mut crate::leanh::LeanObject,
    mut v_k_752_: *mut crate::leanh::LeanObject,
    mut v_nondep_753_: u8,
    mut v_kind_754_: u8,
    mut v___y_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
    mut v___y_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_765_: u8 = 0;
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_a_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_760_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_760_, 0, v_k_752_);
                v___x_761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_749_,
                    v_type_750_,
                    v_val_751_,
                    v___f_760_,
                    v_nondep_753_,
                    v_kind_754_,
                    v___y_755_,
                    v___y_756_,
                    v___y_757_,
                    v___y_758_,
                );
                if crate::leanh::lean_obj_tag(v___x_761_) == 0 {
                    v_a_762_ = crate::leanh::lean_ctor_get(v___x_761_, 0);
                    v_isSharedCheck_769_ = (!crate::leanh::lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_769_ == 0 {
                        v___x_764_ = v___x_761_;
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_762_);
                        crate::leanh::lean_dec(v___x_761_);
                        v___x_764_ = crate::leanh::lean_box(0);
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_770_ = crate::leanh::lean_ctor_get(v___x_761_, 0);
                    v_isSharedCheck_777_ = (!crate::leanh::lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_777_ == 0 {
                        v___x_772_ = v___x_761_;
                        v_isShared_773_ = v_isSharedCheck_777_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_770_);
                        crate::leanh::lean_dec(v___x_761_);
                        v___x_772_ = crate::leanh::lean_box(0);
                        v_isShared_773_ = v_isSharedCheck_777_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_765_ == 0 {
                    v___x_767_ = v___x_764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
                    v___x_767_ = v_reuseFailAlloc_768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_767_;
            }
            3 => {
                if v_isShared_773_ == 0 {
                    v___x_775_ = v___x_772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
                    v___x_775_ = v_reuseFailAlloc_776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___boxed(
    mut v_name_778_: *mut crate::leanh::LeanObject,
    mut v_type_779_: *mut crate::leanh::LeanObject,
    mut v_val_780_: *mut crate::leanh::LeanObject,
    mut v_k_781_: *mut crate::leanh::LeanObject,
    mut v_nondep_782_: *mut crate::leanh::LeanObject,
    mut v_kind_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_789_: u8 = 0;
    let mut v_kind_boxed_790_: u8 = 0;
    let mut v_res_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_789_ = (crate::leanh::lean_unbox(v_nondep_782_) as u8);
    v_kind_boxed_790_ = (crate::leanh::lean_unbox(v_kind_783_) as u8);
    v_res_791_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_778_, v_type_779_, v_val_780_, v_k_781_, v_nondep_boxed_789_, v_kind_boxed_790_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
    crate::leanh::lean_dec(v___y_787_);
    crate::leanh::lean_dec_ref(v___y_786_);
    crate::leanh::lean_dec(v___y_785_);
    crate::leanh::lean_dec_ref(v___y_784_);
    return v_res_791_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(
    mut v_00_u03b1_792_: *mut crate::leanh::LeanObject,
    mut v_name_793_: *mut crate::leanh::LeanObject,
    mut v_type_794_: *mut crate::leanh::LeanObject,
    mut v_val_795_: *mut crate::leanh::LeanObject,
    mut v_k_796_: *mut crate::leanh::LeanObject,
    mut v_nondep_797_: u8,
    mut v_kind_798_: u8,
    mut v___y_799_: *mut crate::leanh::LeanObject,
    mut v___y_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
    mut v___y_802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_793_, v_type_794_, v_val_795_, v_k_796_, v_nondep_797_, v_kind_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
    return v___x_804_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(
    mut v_00_u03b1_805_: *mut crate::leanh::LeanObject,
    mut v_name_806_: *mut crate::leanh::LeanObject,
    mut v_type_807_: *mut crate::leanh::LeanObject,
    mut v_val_808_: *mut crate::leanh::LeanObject,
    mut v_k_809_: *mut crate::leanh::LeanObject,
    mut v_nondep_810_: *mut crate::leanh::LeanObject,
    mut v_kind_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
    mut v___y_814_: *mut crate::leanh::LeanObject,
    mut v___y_815_: *mut crate::leanh::LeanObject,
    mut v___y_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_817_: u8 = 0;
    let mut v_kind_boxed_818_: u8 = 0;
    let mut v_res_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_817_ = (crate::leanh::lean_unbox(v_nondep_810_) as u8);
    v_kind_boxed_818_ = (crate::leanh::lean_unbox(v_kind_811_) as u8);
    v_res_819_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(v_00_u03b1_805_, v_name_806_, v_type_807_, v_val_808_, v_k_809_, v_nondep_boxed_817_, v_kind_boxed_818_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
    crate::leanh::lean_dec(v___y_815_);
    crate::leanh::lean_dec_ref(v___y_814_);
    crate::leanh::lean_dec(v___y_813_);
    crate::leanh::lean_dec_ref(v___y_812_);
    return v_res_819_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(
    mut v_i_820_: *mut crate::leanh::LeanObject,
    mut v_insts_821_: *mut crate::leanh::LeanObject,
    mut v_xs_822_: *mut crate::leanh::LeanObject,
    mut v_k_823_: *mut crate::leanh::LeanObject,
    mut v_inst_824_: *mut crate::leanh::LeanObject,
    mut v___y_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
    mut v___y_827_: *mut crate::leanh::LeanObject,
    mut v___y_828_: *mut crate::leanh::LeanObject,
    mut v___y_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_820_, v_insts_821_, v_xs_822_, v_k_823_, v_inst_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
    crate::leanh::lean_dec(v___y_828_);
    crate::leanh::lean_dec_ref(v___y_827_);
    crate::leanh::lean_dec(v___y_826_);
    crate::leanh::lean_dec_ref(v___y_825_);
    crate::leanh::lean_dec(v_i_820_);
    return v_res_830_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(
    mut v_xs_841_: *mut crate::leanh::LeanObject,
    mut v_k_842_: *mut crate::leanh::LeanObject,
    mut v_i_843_: *mut crate::leanh::LeanObject,
    mut v_insts_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_a_846_: *mut crate::leanh::LeanObject,
    mut v_a_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_878_: u8 = 0;
    let mut v_a_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_850_ = lean_array_get_size(v_xs_841_);
                v___x_851_ = lean_nat_dec_lt(v_i_843_, v___x_850_);
                if v___x_851_ == 0 {
                    crate::leanh::lean_dec(v_i_843_);
                    crate::leanh::lean_dec_ref(v_xs_841_);
                    crate::leanh::lean_inc(v_a_848_);
                    crate::leanh::lean_inc_ref(v_a_847_);
                    crate::leanh::lean_inc(v_a_846_);
                    crate::leanh::lean_inc_ref(v_a_845_);
                    v___x_852_ = crate::leanh::lean_apply_6(
                        v_k_842_,
                        v_insts_844_,
                        v_a_845_,
                        v_a_846_,
                        v_a_847_,
                        v_a_848_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_852_;
                } else {
                    v_x_853_ = lean_array_fget(v_xs_841_, v_i_843_);
                    crate::leanh::lean_inc(v_a_848_);
                    crate::leanh::lean_inc_ref(v_a_847_);
                    crate::leanh::lean_inc(v_a_846_);
                    crate::leanh::lean_inc_ref(v_a_845_);
                    crate::leanh::lean_inc(v_x_853_);
                    v___x_854_ = lean_infer_type(v_x_853_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                    if crate::leanh::lean_obj_tag(v___x_854_) == 0 {
                        v_a_855_ = crate::leanh::lean_ctor_get(v___x_854_, 0);
                        crate::leanh::lean_inc_n(v_a_855_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_854_, 1);
                        v___x_856_ =
                            l_Lean_Meta_getLevel(v_a_855_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                        if crate::leanh::lean_obj_tag(v___x_856_) == 0 {
                            v_a_857_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                            crate::leanh::lean_inc(v_a_857_);
                            crate::leanh::lean_dec_ref_known(v___x_856_, 1);
                            v___f_858_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                            crate::leanh::lean_closure_set(v___f_858_, 0, v_i_843_);
                            crate::leanh::lean_closure_set(v___f_858_, 1, v_insts_844_);
                            crate::leanh::lean_closure_set(v___f_858_, 2, v_xs_841_);
                            crate::leanh::lean_closure_set(v___f_858_, 3, v_k_842_);
                            v___x_859_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1;
                            v___x_860_ = crate::leanh::lean_box(0);
                            v___x_861_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_861_, 0, v_a_857_);
                            crate::leanh::lean_ctor_set(v___x_861_, 1, v___x_860_);
                            crate::leanh::lean_inc_ref(v___x_861_);
                            v___x_862_ = l_Lean_Expr_const___override(v___x_859_, v___x_861_);
                            crate::leanh::lean_inc(v_a_855_);
                            v___x_863_ = l_Lean_Expr_app___override(v___x_862_, v_a_855_);
                            v___x_864_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3;
                            v___x_865_ = l_Lean_Expr_const___override(v___x_864_, v___x_861_);
                            v___x_866_ = l_Lean_mkAppB(v___x_865_, v_a_855_, v_x_853_);
                            v___x_867_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5;
                            v___x_868_ = 0;
                            v___x_869_ = 0;
                            v___x_870_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v___x_867_, v___x_863_, v___x_866_, v___f_858_, v___x_868_, v___x_869_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                            return v___x_870_;
                        } else {
                            crate::leanh::lean_dec(v_a_855_);
                            crate::leanh::lean_dec(v_x_853_);
                            crate::leanh::lean_dec_ref(v_insts_844_);
                            crate::leanh::lean_dec(v_i_843_);
                            crate::leanh::lean_dec_ref(v_k_842_);
                            crate::leanh::lean_dec_ref(v_xs_841_);
                            v_a_871_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                            v_isSharedCheck_878_ =
                                (!crate::leanh::lean_is_exclusive(v___x_856_)) as u8;
                            if v_isSharedCheck_878_ == 0 {
                                v___x_873_ = v___x_856_;
                                v_isShared_874_ = v_isSharedCheck_878_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_871_);
                                crate::leanh::lean_dec(v___x_856_);
                                v___x_873_ = crate::leanh::lean_box(0);
                                v_isShared_874_ = v_isSharedCheck_878_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_853_);
                        crate::leanh::lean_dec_ref(v_insts_844_);
                        crate::leanh::lean_dec(v_i_843_);
                        crate::leanh::lean_dec_ref(v_k_842_);
                        crate::leanh::lean_dec_ref(v_xs_841_);
                        v_a_879_ = crate::leanh::lean_ctor_get(v___x_854_, 0);
                        v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v___x_854_)) as u8;
                        if v_isSharedCheck_886_ == 0 {
                            v___x_881_ = v___x_854_;
                            v_isShared_882_ = v_isSharedCheck_886_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_879_);
                            crate::leanh::lean_dec(v___x_854_);
                            v___x_881_ = crate::leanh::lean_box(0);
                            v_isShared_882_ = v_isSharedCheck_886_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_874_ == 0 {
                    v___x_876_ = v___x_873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
                    v___x_876_ = v_reuseFailAlloc_877_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_876_;
            }
            3 => {
                if v_isShared_882_ == 0 {
                    v___x_884_ = v___x_881_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
                    v___x_884_ = v_reuseFailAlloc_885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(
    mut v_i_887_: *mut crate::leanh::LeanObject,
    mut v_insts_888_: *mut crate::leanh::LeanObject,
    mut v_xs_889_: *mut crate::leanh::LeanObject,
    mut v_k_890_: *mut crate::leanh::LeanObject,
    mut v_inst_891_: *mut crate::leanh::LeanObject,
    mut v___y_892_: *mut crate::leanh::LeanObject,
    mut v___y_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_898_ = lean_nat_add(v_i_887_, v___x_897_);
    v___x_899_ = lean_array_push(v_insts_888_, v_inst_891_);
    v___x_900_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_889_, v_k_890_, v___x_898_, v___x_899_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
    return v___x_900_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(
    mut v_xs_901_: *mut crate::leanh::LeanObject,
    mut v_k_902_: *mut crate::leanh::LeanObject,
    mut v_i_903_: *mut crate::leanh::LeanObject,
    mut v_insts_904_: *mut crate::leanh::LeanObject,
    mut v_a_905_: *mut crate::leanh::LeanObject,
    mut v_a_906_: *mut crate::leanh::LeanObject,
    mut v_a_907_: *mut crate::leanh::LeanObject,
    mut v_a_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_901_, v_k_902_, v_i_903_, v_insts_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
    crate::leanh::lean_dec(v_a_908_);
    crate::leanh::lean_dec_ref(v_a_907_);
    crate::leanh::lean_dec(v_a_906_);
    crate::leanh::lean_dec_ref(v_a_905_);
    return v_res_910_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(
    mut v_00_u03b1_911_: *mut crate::leanh::LeanObject,
    mut v_xs_912_: *mut crate::leanh::LeanObject,
    mut v_k_913_: *mut crate::leanh::LeanObject,
    mut v_i_914_: *mut crate::leanh::LeanObject,
    mut v_insts_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_912_, v_k_913_, v_i_914_, v_insts_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
    return v___x_921_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(
    mut v_00_u03b1_922_: *mut crate::leanh::LeanObject,
    mut v_xs_923_: *mut crate::leanh::LeanObject,
    mut v_k_924_: *mut crate::leanh::LeanObject,
    mut v_i_925_: *mut crate::leanh::LeanObject,
    mut v_insts_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_932_ =
        l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(
            v_00_u03b1_922_,
            v_xs_923_,
            v_k_924_,
            v_i_925_,
            v_insts_926_,
            v_a_927_,
            v_a_928_,
            v_a_929_,
            v_a_930_,
        );
    crate::leanh::lean_dec(v_a_930_);
    crate::leanh::lean_dec_ref(v_a_929_);
    crate::leanh::lean_dec(v_a_928_);
    crate::leanh::lean_dec_ref(v_a_927_);
    return v_res_932_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(
    mut v_xs_935_: *mut crate::leanh::LeanObject,
    mut v_k_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
    mut v_a_938_: *mut crate::leanh::LeanObject,
    mut v_a_939_: *mut crate::leanh::LeanObject,
    mut v_a_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_942_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_943_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0;
    v___x_944_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_935_, v_k_936_, v___x_942_, v___x_943_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
    return v___x_944_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(
    mut v_xs_945_: *mut crate::leanh::LeanObject,
    mut v_k_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_945_, v_k_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
    crate::leanh::lean_dec(v_a_950_);
    crate::leanh::lean_dec_ref(v_a_949_);
    crate::leanh::lean_dec(v_a_948_);
    crate::leanh::lean_dec_ref(v_a_947_);
    return v_res_952_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(
    mut v_00_u03b1_953_: *mut crate::leanh::LeanObject,
    mut v_xs_954_: *mut crate::leanh::LeanObject,
    mut v_k_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
    mut v_a_957_: *mut crate::leanh::LeanObject,
    mut v_a_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_961_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_954_, v_k_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
    return v___x_961_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(
    mut v_00_u03b1_962_: *mut crate::leanh::LeanObject,
    mut v_xs_963_: *mut crate::leanh::LeanObject,
    mut v_k_964_: *mut crate::leanh::LeanObject,
    mut v_a_965_: *mut crate::leanh::LeanObject,
    mut v_a_966_: *mut crate::leanh::LeanObject,
    mut v_a_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ =
        l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(
            v_00_u03b1_962_,
            v_xs_963_,
            v_k_964_,
            v_a_965_,
            v_a_966_,
            v_a_967_,
            v_a_968_,
        );
    crate::leanh::lean_dec(v_a_968_);
    crate::leanh::lean_dec_ref(v_a_967_);
    crate::leanh::lean_dec(v_a_966_);
    crate::leanh::lean_dec_ref(v_a_965_);
    return v_res_970_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
    mut v_type_971_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_972_: u8,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_980_: u8 = 0;
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u8 = 0;
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_992_: u8 = 0;
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_997_: u8 = 0;
    let mut v_a_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useOfNonempty_972_ == 0 {
                    v___x_988_ =
                        l_Lean_Meta_mkDefault(v_type_971_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
                    if crate::leanh::lean_obj_tag(v___x_988_) == 0 {
                        v_a_989_ = crate::leanh::lean_ctor_get(v___x_988_, 0);
                        v_isSharedCheck_997_ = (!crate::leanh::lean_is_exclusive(v___x_988_)) as u8;
                        if v_isSharedCheck_997_ == 0 {
                            v___x_991_ = v___x_988_;
                            v_isShared_992_ = v_isSharedCheck_997_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_989_);
                            crate::leanh::lean_dec(v___x_988_);
                            v___x_991_ = crate::leanh::lean_box(0);
                            v_isShared_992_ = v_isSharedCheck_997_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_998_ = crate::leanh::lean_ctor_get(v___x_988_, 0);
                        crate::leanh::lean_inc(v_a_998_);
                        crate::leanh::lean_dec_ref_known(v___x_988_, 1);
                        v_a_985_ = v_a_998_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_999_ = l_Lean_Meta_mkOfNonempty(
                        v_type_971_,
                        v_a_973_,
                        v_a_974_,
                        v_a_975_,
                        v_a_976_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_999_) == 0 {
                        v_a_1000_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                        v_isSharedCheck_1008_ =
                            (!crate::leanh::lean_is_exclusive(v___x_999_)) as u8;
                        if v_isSharedCheck_1008_ == 0 {
                            v___x_1002_ = v___x_999_;
                            v_isShared_1003_ = v_isSharedCheck_1008_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1000_);
                            crate::leanh::lean_dec(v___x_999_);
                            v___x_1002_ = crate::leanh::lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1008_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1009_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                        crate::leanh::lean_inc(v_a_1009_);
                        crate::leanh::lean_dec_ref_known(v___x_999_, 1);
                        v_a_985_ = v_a_1009_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_980_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_979_);
                    v___x_981_ = crate::leanh::lean_box(0);
                    v___x_982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
                    return v___x_982_;
                } else {
                    v___x_983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_983_, 0, v___y_979_);
                    return v___x_983_;
                }
            }
            2 => {
                v___x_986_ = l_Lean_Exception_isInterrupt(v_a_985_);
                if v___x_986_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_985_);
                    v___x_987_ = l_Lean_Exception_isRuntime(v_a_985_);
                    v___y_979_ = v_a_985_;
                    v___y_980_ = v___x_987_;
                    state = 1;
                    continue;
                } else {
                    v___y_979_ = v_a_985_;
                    v___y_980_ = v___x_986_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_993_, 0, v_a_989_);
                if v_isShared_992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_993_);
                    v___x_995_ = v___x_991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
                    v___x_995_ = v_reuseFailAlloc_996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_995_;
            }
            5 => {
                v___x_1004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1004_, 0, v_a_1000_);
                if v_isShared_1003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
                    v___x_1006_ = v_reuseFailAlloc_1007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(
    mut v_type_1010_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1017_: u8 = 0;
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1017_ = (crate::leanh::lean_unbox(v_useOfNonempty_1011_) as u8);
    v_res_1018_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
        v_type_1010_,
        v_useOfNonempty_boxed_1017_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
    );
    crate::leanh::lean_dec(v_a_1015_);
    crate::leanh::lean_dec_ref(v_a_1014_);
    crate::leanh::lean_dec(v_a_1013_);
    crate::leanh::lean_dec_ref(v_a_1012_);
    return v_res_1018_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(
    mut v_k_1019_: *mut crate::leanh::LeanObject,
    mut v_b_1020_: *mut crate::leanh::LeanObject,
    mut v_c_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1025_);
    crate::leanh::lean_inc_ref(v___y_1024_);
    crate::leanh::lean_inc(v___y_1023_);
    crate::leanh::lean_inc_ref(v___y_1022_);
    v___x_1027_ = crate::leanh::lean_apply_7(
        v_k_1019_,
        v_b_1020_,
        v_c_1021_,
        v___y_1022_,
        v___y_1023_,
        v___y_1024_,
        v___y_1025_,
        crate::leanh::lean_box(0),
    );
    return v___x_1027_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(
    mut v_k_1028_: *mut crate::leanh::LeanObject,
    mut v_b_1029_: *mut crate::leanh::LeanObject,
    mut v_c_1030_: *mut crate::leanh::LeanObject,
    mut v___y_1031_: *mut crate::leanh::LeanObject,
    mut v___y_1032_: *mut crate::leanh::LeanObject,
    mut v___y_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_1028_, v_b_1029_, v_c_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
    crate::leanh::lean_dec(v___y_1034_);
    crate::leanh::lean_dec_ref(v___y_1033_);
    crate::leanh::lean_dec(v___y_1032_);
    crate::leanh::lean_dec_ref(v___y_1031_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(
    mut v_type_1037_: *mut crate::leanh::LeanObject,
    mut v_k_1038_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1039_: u8,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
    mut v___y_1041_: *mut crate::leanh::LeanObject,
    mut v___y_1042_: *mut crate::leanh::LeanObject,
    mut v___y_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1045_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1045_, 0, v_k_1038_);
                v___x_1046_ = 0;
                v___x_1047_ = crate::leanh::lean_box(0);
                v___x_1048_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_1046_,
                        v___x_1047_,
                        v_type_1037_,
                        v___f_1045_,
                        v_cleanupAnnotations_1039_,
                        v___x_1046_,
                        v___y_1040_,
                        v___y_1041_,
                        v___y_1042_,
                        v___y_1043_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1048_) == 0 {
                    v_a_1049_ = crate::leanh::lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1056_ = (!crate::leanh::lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1051_ = v___x_1048_;
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1049_);
                        crate::leanh::lean_dec(v___x_1048_);
                        v___x_1051_ = crate::leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1057_ = crate::leanh::lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1064_ = (!crate::leanh::lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1064_ == 0 {
                        v___x_1059_ = v___x_1048_;
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1057_);
                        crate::leanh::lean_dec(v___x_1048_);
                        v___x_1059_ = crate::leanh::lean_box(0);
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1052_ == 0 {
                    v___x_1054_ = v___x_1051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1054_;
            }
            3 => {
                if v_isShared_1060_ == 0 {
                    v___x_1062_ = v___x_1059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
                    v___x_1062_ = v_reuseFailAlloc_1063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___boxed(
    mut v_type_1065_: *mut crate::leanh::LeanObject,
    mut v_k_1066_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1073_: u8 = 0;
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1073_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1067_) as u8);
    v_res_1074_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_1065_, v_k_1066_, v_cleanupAnnotations_boxed_1073_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
    crate::leanh::lean_dec(v___y_1071_);
    crate::leanh::lean_dec_ref(v___y_1070_);
    crate::leanh::lean_dec(v___y_1069_);
    crate::leanh::lean_dec_ref(v___y_1068_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(
    mut v_00_u03b1_1075_: *mut crate::leanh::LeanObject,
    mut v_type_1076_: *mut crate::leanh::LeanObject,
    mut v_k_1077_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1078_: u8,
    mut v___y_1079_: *mut crate::leanh::LeanObject,
    mut v___y_1080_: *mut crate::leanh::LeanObject,
    mut v___y_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_1076_, v_k_1077_, v_cleanupAnnotations_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
    return v___x_1084_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(
    mut v_00_u03b1_1085_: *mut crate::leanh::LeanObject,
    mut v_type_1086_: *mut crate::leanh::LeanObject,
    mut v_k_1087_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1094_: u8 = 0;
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1094_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1088_) as u8);
    v_res_1095_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(v_00_u03b1_1085_, v_type_1086_, v_k_1087_, v_cleanupAnnotations_boxed_1094_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
    crate::leanh::lean_dec(v___y_1092_);
    crate::leanh::lean_dec_ref(v___y_1091_);
    crate::leanh::lean_dec(v___y_1090_);
    crate::leanh::lean_dec_ref(v___y_1089_);
    return v_res_1095_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1102_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1102_, 0, v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1103_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3);
    v___x_1104_ = l_Lean_MessageData_ofFormat(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4);
    v___x_1106_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2;
    v___x_1107_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    crate::leanh::lean_ctor_set(v___x_1107_, 1, v___x_1105_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(
    mut v_ref_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5);
    v___x_1111_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1111_, 0, v_ref_1108_);
    crate::leanh::lean_ctor_set(v___x_1111_, 1, v___x_1110_);
    v___x_1112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1112_, 0, v___x_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(
    mut v_ref_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1113_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(
    mut v_00_u03b1_1116_: *mut crate::leanh::LeanObject,
    mut v_ref_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1117_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(
    mut v_00_u03b1_1124_: *mut crate::leanh::LeanObject,
    mut v_ref_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(v_00_u03b1_1124_, v_ref_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
    crate::leanh::lean_dec(v___y_1129_);
    crate::leanh::lean_dec_ref(v___y_1128_);
    crate::leanh::lean_dec(v___y_1127_);
    crate::leanh::lean_dec_ref(v___y_1126_);
    return v_res_1131_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(
    mut v_xs_1132_: *mut crate::leanh::LeanObject,
    mut v_insts_1133_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1134_: *mut crate::leanh::LeanObject,
    mut v_xs_x27_1135_: *mut crate::leanh::LeanObject,
    mut v_type_x27_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1142_: u8 = 0;
    let mut v_res_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1142_ = (crate::leanh::lean_unbox(v_useOfNonempty_1134_) as u8);
    v_res_1143_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_1132_, v_insts_1133_, v_useOfNonempty_boxed_1142_, v_xs_x27_1135_, v_type_x27_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
    crate::leanh::lean_dec(v___y_1140_);
    crate::leanh::lean_dec_ref(v___y_1139_);
    crate::leanh::lean_dec(v___y_1138_);
    crate::leanh::lean_dec_ref(v___y_1137_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(
    mut v_xs_1144_: *mut crate::leanh::LeanObject,
    mut v_insts_1145_: *mut crate::leanh::LeanObject,
    mut v_type_1146_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1147_: u8,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1165_: u8 = 0;
    let mut v_cancelTk_x3f_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1167_: u8 = 0;
    let mut v_inheritedTraceOptions_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut v_a_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_a_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v_val_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: u8 = 0;
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1153_ = crate::leanh::lean_ctor_get(v_a_1150_, 0);
                crate::leanh::lean_inc_ref(v_fileName_1153_);
                v_fileMap_1154_ = crate::leanh::lean_ctor_get(v_a_1150_, 1);
                crate::leanh::lean_inc_ref(v_fileMap_1154_);
                v_options_1155_ = crate::leanh::lean_ctor_get(v_a_1150_, 2);
                crate::leanh::lean_inc_ref(v_options_1155_);
                v_currRecDepth_1156_ = crate::leanh::lean_ctor_get(v_a_1150_, 3);
                crate::leanh::lean_inc(v_currRecDepth_1156_);
                v_maxRecDepth_1157_ = crate::leanh::lean_ctor_get(v_a_1150_, 4);
                crate::leanh::lean_inc(v_maxRecDepth_1157_);
                v_ref_1158_ = crate::leanh::lean_ctor_get(v_a_1150_, 5);
                crate::leanh::lean_inc(v_ref_1158_);
                v_currNamespace_1159_ = crate::leanh::lean_ctor_get(v_a_1150_, 6);
                crate::leanh::lean_inc(v_currNamespace_1159_);
                v_openDecls_1160_ = crate::leanh::lean_ctor_get(v_a_1150_, 7);
                crate::leanh::lean_inc(v_openDecls_1160_);
                v_initHeartbeats_1161_ = crate::leanh::lean_ctor_get(v_a_1150_, 8);
                crate::leanh::lean_inc(v_initHeartbeats_1161_);
                v_maxHeartbeats_1162_ = crate::leanh::lean_ctor_get(v_a_1150_, 9);
                crate::leanh::lean_inc(v_maxHeartbeats_1162_);
                v_quotContext_1163_ = crate::leanh::lean_ctor_get(v_a_1150_, 10);
                crate::leanh::lean_inc(v_quotContext_1163_);
                v_currMacroScope_1164_ = crate::leanh::lean_ctor_get(v_a_1150_, 11);
                crate::leanh::lean_inc(v_currMacroScope_1164_);
                v_diag_1165_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1166_ = crate::leanh::lean_ctor_get(v_a_1150_, 12);
                crate::leanh::lean_inc(v_cancelTk_x3f_1166_);
                v_suppressElabErrors_1167_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1168_ = crate::leanh::lean_ctor_get(v_a_1150_, 13);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1168_);
                crate::leanh::lean_dec_ref(v_a_1150_);
                v___x_1169_ = crate::leanh::lean_box((v_useOfNonempty_1147_) as usize);
                crate::leanh::lean_inc_ref(v_insts_1145_);
                crate::leanh::lean_inc_ref(v_xs_1144_);
                v___f_1170_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_1170_, 0, v_xs_1144_);
                crate::leanh::lean_closure_set(v___f_1170_, 1, v_insts_1145_);
                crate::leanh::lean_closure_set(v___f_1170_, 2, v___x_1169_);
                v___x_1240_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1241_ = lean_nat_dec_eq(v_maxRecDepth_1157_, v___x_1240_);
                if v___x_1241_ == 0 {
                    v___x_1242_ = lean_nat_dec_eq(v_currRecDepth_1156_, v_maxRecDepth_1157_);
                    if v___x_1242_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_1170_);
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1168_);
                        crate::leanh::lean_dec(v_cancelTk_x3f_1166_);
                        crate::leanh::lean_dec(v_currMacroScope_1164_);
                        crate::leanh::lean_dec(v_quotContext_1163_);
                        crate::leanh::lean_dec(v_maxHeartbeats_1162_);
                        crate::leanh::lean_dec(v_initHeartbeats_1161_);
                        crate::leanh::lean_dec(v_openDecls_1160_);
                        crate::leanh::lean_dec(v_currNamespace_1159_);
                        crate::leanh::lean_dec(v_maxRecDepth_1157_);
                        crate::leanh::lean_dec(v_currRecDepth_1156_);
                        crate::leanh::lean_dec_ref(v_options_1155_);
                        crate::leanh::lean_dec_ref(v_fileMap_1154_);
                        crate::leanh::lean_dec_ref(v_fileName_1153_);
                        crate::leanh::lean_dec_ref(v_type_1146_);
                        crate::leanh::lean_dec_ref(v_insts_1145_);
                        crate::leanh::lean_dec_ref(v_xs_1144_);
                        v___x_1243_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1158_);
                        return v___x_1243_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1172_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1173_ = lean_nat_add(v_currRecDepth_1156_, v___x_1172_);
                crate::leanh::lean_dec(v_currRecDepth_1156_);
                v___x_1174_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1174_, 0, v_fileName_1153_);
                crate::leanh::lean_ctor_set(v___x_1174_, 1, v_fileMap_1154_);
                crate::leanh::lean_ctor_set(v___x_1174_, 2, v_options_1155_);
                crate::leanh::lean_ctor_set(v___x_1174_, 3, v___x_1173_);
                crate::leanh::lean_ctor_set(v___x_1174_, 4, v_maxRecDepth_1157_);
                crate::leanh::lean_ctor_set(v___x_1174_, 5, v_ref_1158_);
                crate::leanh::lean_ctor_set(v___x_1174_, 6, v_currNamespace_1159_);
                crate::leanh::lean_ctor_set(v___x_1174_, 7, v_openDecls_1160_);
                crate::leanh::lean_ctor_set(v___x_1174_, 8, v_initHeartbeats_1161_);
                crate::leanh::lean_ctor_set(v___x_1174_, 9, v_maxHeartbeats_1162_);
                crate::leanh::lean_ctor_set(v___x_1174_, 10, v_quotContext_1163_);
                crate::leanh::lean_ctor_set(v___x_1174_, 11, v_currMacroScope_1164_);
                crate::leanh::lean_ctor_set(v___x_1174_, 12, v_cancelTk_x3f_1166_);
                crate::leanh::lean_ctor_set(v___x_1174_, 13, v_inheritedTraceOptions_1168_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_1165_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1167_,
                );
                crate::leanh::lean_inc_ref(v_type_1146_);
                v___x_1175_ =
                    l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
                        v_type_1146_,
                        v_useOfNonempty_1147_,
                        v_a_1148_,
                        v_a_1149_,
                        v___x_1174_,
                        v_a_1151_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1175_) == 0 {
                    v_a_1176_ = crate::leanh::lean_ctor_get(v___x_1175_, 0);
                    crate::leanh::lean_inc(v_a_1176_);
                    crate::leanh::lean_dec_ref_known(v___x_1175_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1176_) == 1 {
                        crate::leanh::lean_dec_ref(v___f_1170_);
                        crate::leanh::lean_dec_ref(v_type_1146_);
                        v_val_1177_ = crate::leanh::lean_ctor_get(v_a_1176_, 0);
                        v_isSharedCheck_1214_ = (!crate::leanh::lean_is_exclusive(v_a_1176_)) as u8;
                        if v_isSharedCheck_1214_ == 0 {
                            v___x_1179_ = v_a_1176_;
                            v_isShared_1180_ = v_isSharedCheck_1214_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1177_);
                            crate::leanh::lean_dec(v_a_1176_);
                            v___x_1179_ = crate::leanh::lean_box(0);
                            v_isShared_1180_ = v_isSharedCheck_1214_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1176_);
                        v___x_1215_ = l_Lean_Meta_whnfCore(
                            v_type_1146_,
                            v_a_1148_,
                            v_a_1149_,
                            v___x_1174_,
                            v_a_1151_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1215_) == 0 {
                            v_a_1216_ = crate::leanh::lean_ctor_get(v___x_1215_, 0);
                            crate::leanh::lean_inc(v_a_1216_);
                            crate::leanh::lean_dec_ref_known(v___x_1215_, 1);
                            v___x_1217_ = l_Lean_Expr_isForall(v_a_1216_);
                            if v___x_1217_ == 0 {
                                crate::leanh::lean_dec_ref(v___f_1170_);
                                v___x_1218_ = l_Lean_Meta_unfoldDefinition_x3f(
                                    v_a_1216_,
                                    v___x_1217_,
                                    v_a_1148_,
                                    v_a_1149_,
                                    v___x_1174_,
                                    v_a_1151_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1218_) == 0 {
                                    v_a_1219_ = crate::leanh::lean_ctor_get(v___x_1218_, 0);
                                    v_isSharedCheck_1229_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1218_)) as u8;
                                    if v_isSharedCheck_1229_ == 0 {
                                        v___x_1221_ = v___x_1218_;
                                        v_isShared_1222_ = v_isSharedCheck_1229_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1219_);
                                        crate::leanh::lean_dec(v___x_1218_);
                                        v___x_1221_ = crate::leanh::lean_box(0);
                                        v_isShared_1222_ = v_isSharedCheck_1229_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                                    crate::leanh::lean_dec_ref(v_insts_1145_);
                                    crate::leanh::lean_dec_ref(v_xs_1144_);
                                    return v___x_1218_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_insts_1145_);
                                crate::leanh::lean_dec_ref(v_xs_1144_);
                                v___x_1230_ = 0;
                                v___x_1231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_a_1216_, v___f_1170_, v___x_1230_, v_a_1148_, v_a_1149_, v___x_1174_, v_a_1151_);
                                crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                                return v___x_1231_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                            crate::leanh::lean_dec_ref(v___f_1170_);
                            crate::leanh::lean_dec_ref(v_insts_1145_);
                            crate::leanh::lean_dec_ref(v_xs_1144_);
                            v_a_1232_ = crate::leanh::lean_ctor_get(v___x_1215_, 0);
                            v_isSharedCheck_1239_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1215_)) as u8;
                            if v_isSharedCheck_1239_ == 0 {
                                v___x_1234_ = v___x_1215_;
                                v_isShared_1235_ = v_isSharedCheck_1239_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1232_);
                                crate::leanh::lean_dec(v___x_1215_);
                                v___x_1234_ = crate::leanh::lean_box(0);
                                v_isShared_1235_ = v_isSharedCheck_1239_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                    crate::leanh::lean_dec_ref(v___f_1170_);
                    crate::leanh::lean_dec_ref(v_type_1146_);
                    crate::leanh::lean_dec_ref(v_insts_1145_);
                    crate::leanh::lean_dec_ref(v_xs_1144_);
                    return v___x_1175_;
                }
            }
            2 => {
                v___x_1181_ = 1;
                v___x_1182_ = 1;
                v___x_1183_ = l_Lean_Meta_mkLetFVars(
                    v_insts_1145_,
                    v_val_1177_,
                    v___x_1181_,
                    v___x_1181_,
                    v___x_1182_,
                    v_a_1148_,
                    v_a_1149_,
                    v___x_1174_,
                    v_a_1151_,
                );
                crate::leanh::lean_dec_ref(v_insts_1145_);
                if crate::leanh::lean_obj_tag(v___x_1183_) == 0 {
                    v_a_1184_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                    crate::leanh::lean_inc(v_a_1184_);
                    crate::leanh::lean_dec_ref_known(v___x_1183_, 1);
                    v___x_1185_ = 0;
                    v___x_1186_ = l_Lean_Meta_mkLambdaFVars(
                        v_xs_1144_,
                        v_a_1184_,
                        v___x_1185_,
                        v___x_1181_,
                        v___x_1185_,
                        v___x_1181_,
                        v___x_1182_,
                        v_a_1148_,
                        v_a_1149_,
                        v___x_1174_,
                        v_a_1151_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                    crate::leanh::lean_dec_ref(v_xs_1144_);
                    if crate::leanh::lean_obj_tag(v___x_1186_) == 0 {
                        v_a_1187_ = crate::leanh::lean_ctor_get(v___x_1186_, 0);
                        v_isSharedCheck_1197_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1186_)) as u8;
                        if v_isSharedCheck_1197_ == 0 {
                            v___x_1189_ = v___x_1186_;
                            v_isShared_1190_ = v_isSharedCheck_1197_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1187_);
                            crate::leanh::lean_dec(v___x_1186_);
                            v___x_1189_ = crate::leanh::lean_box(0);
                            v_isShared_1190_ = v_isSharedCheck_1197_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1179_);
                        v_a_1198_ = crate::leanh::lean_ctor_get(v___x_1186_, 0);
                        v_isSharedCheck_1205_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1186_)) as u8;
                        if v_isSharedCheck_1205_ == 0 {
                            v___x_1200_ = v___x_1186_;
                            v_isShared_1201_ = v_isSharedCheck_1205_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1198_);
                            crate::leanh::lean_dec(v___x_1186_);
                            v___x_1200_ = crate::leanh::lean_box(0);
                            v_isShared_1201_ = v_isSharedCheck_1205_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1179_);
                    crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                    crate::leanh::lean_dec_ref(v_xs_1144_);
                    v_a_1206_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                    v_isSharedCheck_1213_ = (!crate::leanh::lean_is_exclusive(v___x_1183_)) as u8;
                    if v_isSharedCheck_1213_ == 0 {
                        v___x_1208_ = v___x_1183_;
                        v_isShared_1209_ = v_isSharedCheck_1213_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1206_);
                        crate::leanh::lean_dec(v___x_1183_);
                        v___x_1208_ = crate::leanh::lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1213_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1179_, 0, v_a_1187_);
                    v___x_1192_ = v___x_1179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1187_);
                    v___x_1192_ = v_reuseFailAlloc_1196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1189_, 0, v___x_1192_);
                    v___x_1194_ = v___x_1189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
                    v___x_1194_ = v_reuseFailAlloc_1195_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1194_;
            }
            6 => {
                if v_isShared_1201_ == 0 {
                    v___x_1203_ = v___x_1200_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
                    v___x_1203_ = v_reuseFailAlloc_1204_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1203_;
            }
            8 => {
                if v_isShared_1209_ == 0 {
                    v___x_1211_ = v___x_1208_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1211_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_1219_) == 1 {
                    crate::leanh::lean_del_object(v___x_1221_);
                    v_val_1223_ = crate::leanh::lean_ctor_get(v_a_1219_, 0);
                    crate::leanh::lean_inc(v_val_1223_);
                    crate::leanh::lean_dec_ref_known(v_a_1219_, 1);
                    v_type_1146_ = v_val_1223_;
                    v_a_1150_ = v___x_1174_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1219_);
                    crate::leanh::lean_dec_ref_known(v___x_1174_, 14);
                    crate::leanh::lean_dec_ref(v_insts_1145_);
                    crate::leanh::lean_dec_ref(v_xs_1144_);
                    v___x_1225_ = crate::leanh::lean_box(0);
                    if v_isShared_1222_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1221_, 0, v___x_1225_);
                        v___x_1227_ = v___x_1221_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
                        v___x_1227_ = v_reuseFailAlloc_1228_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_1227_;
            }
            12 => {
                if v_isShared_1235_ == 0 {
                    v___x_1237_ = v___x_1234_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
                    v___x_1237_ = v_reuseFailAlloc_1238_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(
    mut v_xs_1244_: *mut crate::leanh::LeanObject,
    mut v_xs_x27_1245_: *mut crate::leanh::LeanObject,
    mut v_insts_1246_: *mut crate::leanh::LeanObject,
    mut v_type_x27_1247_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1248_: u8,
    mut v_insts_x27_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Array_append___redArg(v_xs_1244_, v_xs_x27_1245_);
    v___x_1256_ = l_Array_append___redArg(v_insts_1246_, v_insts_x27_1249_);
    crate::leanh::lean_inc_ref(v___y_1252_);
    v___x_1257_ =
        l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(
            v___x_1255_,
            v___x_1256_,
            v_type_x27_1247_,
            v_useOfNonempty_1248_,
            v___y_1250_,
            v___y_1251_,
            v___y_1252_,
            v___y_1253_,
        );
    return v___x_1257_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed(
    mut v_xs_1258_: *mut crate::leanh::LeanObject,
    mut v_xs_x27_1259_: *mut crate::leanh::LeanObject,
    mut v_insts_1260_: *mut crate::leanh::LeanObject,
    mut v_type_x27_1261_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1262_: *mut crate::leanh::LeanObject,
    mut v_insts_x27_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1269_: u8 = 0;
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1269_ = (crate::leanh::lean_unbox(v_useOfNonempty_1262_) as u8);
    v_res_1270_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_1258_, v_xs_x27_1259_, v_insts_1260_, v_type_x27_1261_, v_useOfNonempty_boxed_1269_, v_insts_x27_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    crate::leanh::lean_dec(v___y_1267_);
    crate::leanh::lean_dec_ref(v___y_1266_);
    crate::leanh::lean_dec(v___y_1265_);
    crate::leanh::lean_dec_ref(v___y_1264_);
    crate::leanh::lean_dec_ref(v_insts_x27_1263_);
    crate::leanh::lean_dec_ref(v_xs_x27_1259_);
    return v_res_1270_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(
    mut v_xs_1271_: *mut crate::leanh::LeanObject,
    mut v_insts_1272_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1273_: u8,
    mut v_xs_x27_1274_: *mut crate::leanh::LeanObject,
    mut v_type_x27_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = crate::leanh::lean_box((v_useOfNonempty_1273_) as usize);
    crate::leanh::lean_inc_ref(v_xs_x27_1274_);
    v___f_1282_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
    crate::leanh::lean_closure_set(v___f_1282_, 0, v_xs_1271_);
    crate::leanh::lean_closure_set(v___f_1282_, 1, v_xs_x27_1274_);
    crate::leanh::lean_closure_set(v___f_1282_, 2, v_insts_1272_);
    crate::leanh::lean_closure_set(v___f_1282_, 3, v_type_x27_1275_);
    crate::leanh::lean_closure_set(v___f_1282_, 4, v___x_1281_);
    v___x_1283_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_x27_1274_, v___f_1282_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
    return v___x_1283_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(
    mut v_xs_1284_: *mut crate::leanh::LeanObject,
    mut v_insts_1285_: *mut crate::leanh::LeanObject,
    mut v_type_1286_: *mut crate::leanh::LeanObject,
    mut v_useOfNonempty_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1293_: u8 = 0;
    let mut v_res_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1293_ = (crate::leanh::lean_unbox(v_useOfNonempty_1287_) as u8);
    v_res_1294_ =
        l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(
            v_xs_1284_,
            v_insts_1285_,
            v_type_1286_,
            v_useOfNonempty_boxed_1293_,
            v_a_1288_,
            v_a_1289_,
            v_a_1290_,
            v_a_1291_,
        );
    crate::leanh::lean_dec(v_a_1291_);
    crate::leanh::lean_dec(v_a_1289_);
    crate::leanh::lean_dec_ref(v_a_1288_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(
    mut v_msgData_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1301_ = lean_st_ref_get(v___y_1299_);
    v_env_1302_ = crate::leanh::lean_ctor_get(v___x_1301_, 0);
    crate::leanh::lean_inc_ref(v_env_1302_);
    crate::leanh::lean_dec(v___x_1301_);
    v___x_1303_ = lean_st_ref_get(v___y_1297_);
    v_mctx_1304_ = crate::leanh::lean_ctor_get(v___x_1303_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1304_);
    crate::leanh::lean_dec(v___x_1303_);
    v_lctx_1305_ = crate::leanh::lean_ctor_get(v___y_1296_, 2);
    v_options_1306_ = crate::leanh::lean_ctor_get(v___y_1298_, 2);
    crate::leanh::lean_inc_ref(v_options_1306_);
    crate::leanh::lean_inc_ref(v_lctx_1305_);
    v___x_1307_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1307_, 0, v_env_1302_);
    crate::leanh::lean_ctor_set(v___x_1307_, 1, v_mctx_1304_);
    crate::leanh::lean_ctor_set(v___x_1307_, 2, v_lctx_1305_);
    crate::leanh::lean_ctor_set(v___x_1307_, 3, v_options_1306_);
    v___x_1308_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1307_);
    crate::leanh::lean_ctor_set(v___x_1308_, 1, v_msgData_1295_);
    v___x_1309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1309_, 0, v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(
    mut v_msgData_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
    crate::leanh::lean_dec(v___y_1314_);
    crate::leanh::lean_dec_ref(v___y_1313_);
    crate::leanh::lean_dec(v___y_1312_);
    crate::leanh::lean_dec_ref(v___y_1311_);
    return v_res_1316_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
    mut v_msg_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1323_ = crate::leanh::lean_ctor_get(v___y_1320_, 5);
                v___x_1324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
                v_a_1325_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                v_isSharedCheck_1333_ = (!crate::leanh::lean_is_exclusive(v___x_1324_)) as u8;
                if v_isSharedCheck_1333_ == 0 {
                    v___x_1327_ = v___x_1324_;
                    v_isShared_1328_ = v_isSharedCheck_1333_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1325_);
                    crate::leanh::lean_dec(v___x_1324_);
                    v___x_1327_ = crate::leanh::lean_box(0);
                    v_isShared_1328_ = v_isSharedCheck_1333_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1323_);
                v___x_1329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1329_, 0, v_ref_1323_);
                crate::leanh::lean_ctor_set(v___x_1329_, 1, v_a_1325_);
                if v_isShared_1328_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1327_, 1);
                    crate::leanh::lean_ctor_set(v___x_1327_, 0, v___x_1329_);
                    v___x_1331_ = v___x_1327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
                    v___x_1331_ = v_reuseFailAlloc_1332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg___boxed(
    mut v_msg_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
        v_msg_1334_,
        v___y_1335_,
        v___y_1336_,
        v___y_1337_,
        v___y_1338_,
    );
    crate::leanh::lean_dec(v___y_1338_);
    crate::leanh::lean_dec_ref(v___y_1337_);
    crate::leanh::lean_dec(v___y_1336_);
    crate::leanh::lean_dec_ref(v___y_1335_);
    return v_res_1340_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__0;
    v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__2;
    v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = 0;
    v___x_1348_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1;
    v___x_1349_ = l_Lean_MessageData_ofConstName(v___x_1348_, v___x_1347_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__5;
    v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = 0;
    v___x_1357_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__8;
    v___x_1358_ = l_Lean_MessageData_ofConstName(v___x_1357_, v___x_1356_);
    return v___x_1358_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__10;
    v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__12;
    v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___lam__0(
    mut v_xs_1365_: *mut crate::leanh::LeanObject,
    mut v_type_1366_: *mut crate::leanh::LeanObject,
    mut v_failedToMessage_1367_: *mut crate::leanh::LeanObject,
    mut v_insts_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: u8 = 0;
    let mut v___y_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v_val_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_a_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1374_ = 0;
                crate::leanh::lean_inc_ref(v___y_1371_);
                crate::leanh::lean_inc_ref(v_type_1366_);
                crate::leanh::lean_inc_ref(v_insts_1368_);
                crate::leanh::lean_inc_ref(v_xs_1365_);
                v___x_1416_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_1365_, v_insts_1368_, v_type_1366_, v___x_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                if crate::leanh::lean_obj_tag(v___x_1416_) == 0 {
                    v_a_1417_ = crate::leanh::lean_ctor_get(v___x_1416_, 0);
                    crate::leanh::lean_inc(v_a_1417_);
                    if crate::leanh::lean_obj_tag(v_a_1417_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1416_, 1);
                        v___x_1418_ = 1;
                        crate::leanh::lean_inc_ref(v___y_1371_);
                        crate::leanh::lean_inc_ref(v_type_1366_);
                        crate::leanh::lean_inc_ref(v_xs_1365_);
                        v___x_1419_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_1365_, v_insts_1368_, v_type_1366_, v___x_1418_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                        v___y_1376_ = v___x_1419_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_1417_, 1);
                        crate::leanh::lean_dec_ref(v_insts_1368_);
                        v___y_1376_ = v___x_1416_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_insts_1368_);
                    v___y_1376_ = v___x_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1376_) == 0 {
                    v_a_1377_ = crate::leanh::lean_ctor_get(v___y_1376_, 0);
                    v_isSharedCheck_1407_ = (!crate::leanh::lean_is_exclusive(v___y_1376_)) as u8;
                    if v_isSharedCheck_1407_ == 0 {
                        v___x_1379_ = v___y_1376_;
                        v_isShared_1380_ = v_isSharedCheck_1407_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1377_);
                        crate::leanh::lean_dec(v___y_1376_);
                        v___x_1379_ = crate::leanh::lean_box(0);
                        v_isShared_1380_ = v_isSharedCheck_1407_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_failedToMessage_1367_);
                    crate::leanh::lean_dec_ref(v_type_1366_);
                    crate::leanh::lean_dec_ref(v_xs_1365_);
                    v_a_1408_ = crate::leanh::lean_ctor_get(v___y_1376_, 0);
                    v_isSharedCheck_1415_ = (!crate::leanh::lean_is_exclusive(v___y_1376_)) as u8;
                    if v_isSharedCheck_1415_ == 0 {
                        v___x_1410_ = v___y_1376_;
                        v_isShared_1411_ = v_isSharedCheck_1415_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1408_);
                        crate::leanh::lean_dec(v___y_1376_);
                        v___x_1410_ = crate::leanh::lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1415_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1377_) == 1 {
                    crate::leanh::lean_dec_ref(v_failedToMessage_1367_);
                    crate::leanh::lean_dec_ref(v_type_1366_);
                    crate::leanh::lean_dec_ref(v_xs_1365_);
                    v_val_1381_ = crate::leanh::lean_ctor_get(v_a_1377_, 0);
                    crate::leanh::lean_inc(v_val_1381_);
                    crate::leanh::lean_dec_ref_known(v_a_1377_, 1);
                    if v_isShared_1380_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1379_, 0, v_val_1381_);
                        v___x_1383_ = v___x_1379_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1384_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_val_1381_);
                        v___x_1383_ = v_reuseFailAlloc_1384_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1379_);
                    crate::leanh::lean_dec(v_a_1377_);
                    v___x_1385_ = 1;
                    v___x_1386_ = 1;
                    v___x_1387_ = l_Lean_Meta_mkForallFVars(
                        v_xs_1365_,
                        v_type_1366_,
                        v___x_1374_,
                        v___x_1385_,
                        v___x_1385_,
                        v___x_1386_,
                        v___y_1369_,
                        v___y_1370_,
                        v___y_1371_,
                        v___y_1372_,
                    );
                    crate::leanh::lean_dec_ref(v_xs_1365_);
                    if crate::leanh::lean_obj_tag(v___x_1387_) == 0 {
                        v_a_1388_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                        crate::leanh::lean_inc(v_a_1388_);
                        crate::leanh::lean_dec_ref_known(v___x_1387_, 1);
                        v___x_1389_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1,
                        );
                        v___x_1390_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1390_, 0, v_failedToMessage_1367_);
                        crate::leanh::lean_ctor_set(v___x_1390_, 1, v___x_1389_);
                        v___x_1391_ = l_Lean_indentExpr(v_a_1388_);
                        v___x_1392_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1390_);
                        crate::leanh::lean_ctor_set(v___x_1392_, 1, v___x_1391_);
                        v___x_1393_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3,
                        );
                        v___x_1394_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1394_, 0, v___x_1392_);
                        crate::leanh::lean_ctor_set(v___x_1394_, 1, v___x_1393_);
                        v___x_1395_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4,
                        );
                        v___x_1396_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1396_, 0, v___x_1394_);
                        crate::leanh::lean_ctor_set(v___x_1396_, 1, v___x_1395_);
                        v___x_1397_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6,
                        );
                        v___x_1398_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1396_);
                        crate::leanh::lean_ctor_set(v___x_1398_, 1, v___x_1397_);
                        v___x_1399_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9,
                        );
                        v___x_1400_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1398_);
                        crate::leanh::lean_ctor_set(v___x_1400_, 1, v___x_1399_);
                        v___x_1401_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11,
                        );
                        v___x_1402_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1402_, 0, v___x_1400_);
                        crate::leanh::lean_ctor_set(v___x_1402_, 1, v___x_1401_);
                        v___x_1403_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1402_);
                        crate::leanh::lean_ctor_set(v___x_1403_, 1, v___x_1395_);
                        v___x_1404_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13,
                        );
                        v___x_1405_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1405_, 0, v___x_1403_);
                        crate::leanh::lean_ctor_set(v___x_1405_, 1, v___x_1404_);
                        v___x_1406_ =
                            l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
                                v___x_1405_,
                                v___y_1369_,
                                v___y_1370_,
                                v___y_1371_,
                                v___y_1372_,
                            );
                        return v___x_1406_;
                    } else {
                        crate::leanh::lean_dec_ref(v_failedToMessage_1367_);
                        return v___x_1387_;
                    }
                }
            }
            3 => {
                return v___x_1383_;
            }
            4 => {
                if v_isShared_1411_ == 0 {
                    v___x_1413_ = v___x_1410_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
                    v___x_1413_ = v_reuseFailAlloc_1414_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___lam__0___boxed(
    mut v_xs_1420_: *mut crate::leanh::LeanObject,
    mut v_type_1421_: *mut crate::leanh::LeanObject,
    mut v_failedToMessage_1422_: *mut crate::leanh::LeanObject,
    mut v_insts_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Lean_Elab_mkInhabitantFor___lam__0(
        v_xs_1420_,
        v_type_1421_,
        v_failedToMessage_1422_,
        v_insts_1423_,
        v___y_1424_,
        v___y_1425_,
        v___y_1426_,
        v___y_1427_,
    );
    crate::leanh::lean_dec(v___y_1427_);
    crate::leanh::lean_dec_ref(v___y_1426_);
    crate::leanh::lean_dec(v___y_1425_);
    crate::leanh::lean_dec_ref(v___y_1424_);
    return v_res_1429_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor(
    mut v_failedToMessage_1430_: *mut crate::leanh::LeanObject,
    mut v_xs_1431_: *mut crate::leanh::LeanObject,
    mut v_type_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
    mut v_a_1435_: *mut crate::leanh::LeanObject,
    mut v_a_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_xs_1431_);
    v___f_1438_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_mkInhabitantFor___lam__0___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1438_, 0, v_xs_1431_);
    crate::leanh::lean_closure_set(v___f_1438_, 1, v_type_1432_);
    crate::leanh::lean_closure_set(v___f_1438_, 2, v_failedToMessage_1430_);
    v___x_1439_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_1431_, v___f_1438_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___boxed(
    mut v_failedToMessage_1440_: *mut crate::leanh::LeanObject,
    mut v_xs_1441_: *mut crate::leanh::LeanObject,
    mut v_type_1442_: *mut crate::leanh::LeanObject,
    mut v_a_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1448_ = l_Lean_Elab_mkInhabitantFor(
        v_failedToMessage_1440_,
        v_xs_1441_,
        v_type_1442_,
        v_a_1443_,
        v_a_1444_,
        v_a_1445_,
        v_a_1446_,
    );
    crate::leanh::lean_dec(v_a_1446_);
    crate::leanh::lean_dec_ref(v_a_1445_);
    crate::leanh::lean_dec(v_a_1444_);
    crate::leanh::lean_dec_ref(v_a_1443_);
    return v_res_1448_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(
    mut v_00_u03b1_1449_: *mut crate::leanh::LeanObject,
    mut v_msg_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
        v_msg_1450_,
        v___y_1451_,
        v___y_1452_,
        v___y_1453_,
        v___y_1454_,
    );
    return v___x_1456_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___boxed(
    mut v_00_u03b1_1457_: *mut crate::leanh::LeanObject,
    mut v_msg_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(
        v_00_u03b1_1457_,
        v_msg_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
    );
    crate::leanh::lean_dec(v___y_1462_);
    crate::leanh::lean_dec_ref(v___y_1461_);
    crate::leanh::lean_dec(v___y_1460_);
    crate::leanh::lean_dec_ref(v___y_1459_);
    return v_res_1464_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_MkInhabitant(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
}
