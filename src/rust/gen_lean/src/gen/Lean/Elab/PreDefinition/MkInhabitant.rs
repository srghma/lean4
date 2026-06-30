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
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut leanh::LeanObject,13340093926952294564 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut leanh::LeanObject,13340093926952294564 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value) as *mut leanh::LeanObject,17998702798483655788 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value) as *mut leanh::LeanObject,6605161548626312362 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value: leanh::LeanStringObject<
    32,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value: leanh::LeanStringObject<
    137,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value)
                as *mut leanh::LeanObject,
            13229434762204987278 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value: leanh::LeanStringObject<
    77,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value: leanh::LeanStringObject<
    182,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(
    mut v_k_733_: *mut leanh::LeanObject,
    mut v_b_734_: *mut leanh::LeanObject,
    mut v___y_735_: *mut leanh::LeanObject,
    mut v___y_736_: *mut leanh::LeanObject,
    mut v___y_737_: *mut leanh::LeanObject,
    mut v___y_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_738_);
    leanh::lean_inc_ref(v___y_737_);
    leanh::lean_inc(v___y_736_);
    leanh::lean_inc_ref(v___y_735_);
    v___x_740_ = leanh::lean_apply_6(
        v_k_733_,
        v_b_734_,
        v___y_735_,
        v___y_736_,
        v___y_737_,
        v___y_738_,
        leanh::lean_box(0),
    );
    return v___x_740_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(
    mut v_k_741_: *mut leanh::LeanObject,
    mut v_b_742_: *mut leanh::LeanObject,
    mut v___y_743_: *mut leanh::LeanObject,
    mut v___y_744_: *mut leanh::LeanObject,
    mut v___y_745_: *mut leanh::LeanObject,
    mut v___y_746_: *mut leanh::LeanObject,
    mut v___y_747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_741_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
    leanh::lean_dec(v___y_746_);
    leanh::lean_dec_ref(v___y_745_);
    leanh::lean_dec(v___y_744_);
    leanh::lean_dec_ref(v___y_743_);
    return v_res_748_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(
    mut v_name_749_: *mut leanh::LeanObject,
    mut v_type_750_: *mut leanh::LeanObject,
    mut v_val_751_: *mut leanh::LeanObject,
    mut v_k_752_: *mut leanh::LeanObject,
    mut v_nondep_753_: u8,
    mut v_kind_754_: u8,
    mut v___y_755_: *mut leanh::LeanObject,
    mut v___y_756_: *mut leanh::LeanObject,
    mut v___y_757_: *mut leanh::LeanObject,
    mut v___y_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_765_: u8 = 0;
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_a_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_760_ = leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_760_, 0, v_k_752_);
                v___x_761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_761_) == 0 {
                    v_a_762_ = leanh::lean_ctor_get(v___x_761_, 0);
                    v_isSharedCheck_769_ = (!leanh::lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_769_ == 0 {
                        v___x_764_ = v___x_761_;
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_762_);
                        leanh::lean_dec(v___x_761_);
                        v___x_764_ = leanh::lean_box(0);
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_770_ = leanh::lean_ctor_get(v___x_761_, 0);
                    v_isSharedCheck_777_ = (!leanh::lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_777_ == 0 {
                        v___x_772_ = v___x_761_;
                        v_isShared_773_ = v_isSharedCheck_777_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_770_);
                        leanh::lean_dec(v___x_761_);
                        v___x_772_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_768_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
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
                    v_reuseFailAlloc_776_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
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
    mut v_name_778_: *mut leanh::LeanObject,
    mut v_type_779_: *mut leanh::LeanObject,
    mut v_val_780_: *mut leanh::LeanObject,
    mut v_k_781_: *mut leanh::LeanObject,
    mut v_nondep_782_: *mut leanh::LeanObject,
    mut v_kind_783_: *mut leanh::LeanObject,
    mut v___y_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
    mut v___y_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_789_: u8 = 0;
    let mut v_kind_boxed_790_: u8 = 0;
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_789_ = (leanh::lean_unbox(v_nondep_782_) as u8);
    v_kind_boxed_790_ = (leanh::lean_unbox(v_kind_783_) as u8);
    v_res_791_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_778_, v_type_779_, v_val_780_, v_k_781_, v_nondep_boxed_789_, v_kind_boxed_790_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
    leanh::lean_dec(v___y_787_);
    leanh::lean_dec_ref(v___y_786_);
    leanh::lean_dec(v___y_785_);
    leanh::lean_dec_ref(v___y_784_);
    return v_res_791_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(
    mut v_00_u03b1_792_: *mut leanh::LeanObject,
    mut v_name_793_: *mut leanh::LeanObject,
    mut v_type_794_: *mut leanh::LeanObject,
    mut v_val_795_: *mut leanh::LeanObject,
    mut v_k_796_: *mut leanh::LeanObject,
    mut v_nondep_797_: u8,
    mut v_kind_798_: u8,
    mut v___y_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
    mut v___y_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_793_, v_type_794_, v_val_795_, v_k_796_, v_nondep_797_, v_kind_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
    return v___x_804_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(
    mut v_00_u03b1_805_: *mut leanh::LeanObject,
    mut v_name_806_: *mut leanh::LeanObject,
    mut v_type_807_: *mut leanh::LeanObject,
    mut v_val_808_: *mut leanh::LeanObject,
    mut v_k_809_: *mut leanh::LeanObject,
    mut v_nondep_810_: *mut leanh::LeanObject,
    mut v_kind_811_: *mut leanh::LeanObject,
    mut v___y_812_: *mut leanh::LeanObject,
    mut v___y_813_: *mut leanh::LeanObject,
    mut v___y_814_: *mut leanh::LeanObject,
    mut v___y_815_: *mut leanh::LeanObject,
    mut v___y_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_817_: u8 = 0;
    let mut v_kind_boxed_818_: u8 = 0;
    let mut v_res_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_817_ = (leanh::lean_unbox(v_nondep_810_) as u8);
    v_kind_boxed_818_ = (leanh::lean_unbox(v_kind_811_) as u8);
    v_res_819_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(v_00_u03b1_805_, v_name_806_, v_type_807_, v_val_808_, v_k_809_, v_nondep_boxed_817_, v_kind_boxed_818_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
    leanh::lean_dec(v___y_815_);
    leanh::lean_dec_ref(v___y_814_);
    leanh::lean_dec(v___y_813_);
    leanh::lean_dec_ref(v___y_812_);
    return v_res_819_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(
    mut v_i_820_: *mut leanh::LeanObject,
    mut v_insts_821_: *mut leanh::LeanObject,
    mut v_xs_822_: *mut leanh::LeanObject,
    mut v_k_823_: *mut leanh::LeanObject,
    mut v_inst_824_: *mut leanh::LeanObject,
    mut v___y_825_: *mut leanh::LeanObject,
    mut v___y_826_: *mut leanh::LeanObject,
    mut v___y_827_: *mut leanh::LeanObject,
    mut v___y_828_: *mut leanh::LeanObject,
    mut v___y_829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_820_, v_insts_821_, v_xs_822_, v_k_823_, v_inst_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
    leanh::lean_dec(v___y_828_);
    leanh::lean_dec_ref(v___y_827_);
    leanh::lean_dec(v___y_826_);
    leanh::lean_dec_ref(v___y_825_);
    leanh::lean_dec(v_i_820_);
    return v_res_830_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(
    mut v_xs_841_: *mut leanh::LeanObject,
    mut v_k_842_: *mut leanh::LeanObject,
    mut v_i_843_: *mut leanh::LeanObject,
    mut v_insts_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
    mut v_a_846_: *mut leanh::LeanObject,
    mut v_a_847_: *mut leanh::LeanObject,
    mut v_a_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_878_: u8 = 0;
    let mut v_a_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_850_ = lean_array_get_size(v_xs_841_);
                v___x_851_ = lean_nat_dec_lt(v_i_843_, v___x_850_);
                if v___x_851_ == 0 {
                    leanh::lean_dec(v_i_843_);
                    leanh::lean_dec_ref(v_xs_841_);
                    leanh::lean_inc(v_a_848_);
                    leanh::lean_inc_ref(v_a_847_);
                    leanh::lean_inc(v_a_846_);
                    leanh::lean_inc_ref(v_a_845_);
                    v___x_852_ = leanh::lean_apply_6(
                        v_k_842_,
                        v_insts_844_,
                        v_a_845_,
                        v_a_846_,
                        v_a_847_,
                        v_a_848_,
                        leanh::lean_box(0),
                    );
                    return v___x_852_;
                } else {
                    v_x_853_ = lean_array_fget(v_xs_841_, v_i_843_);
                    leanh::lean_inc(v_a_848_);
                    leanh::lean_inc_ref(v_a_847_);
                    leanh::lean_inc(v_a_846_);
                    leanh::lean_inc_ref(v_a_845_);
                    leanh::lean_inc(v_x_853_);
                    v___x_854_ = lean_infer_type(v_x_853_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                    if leanh::lean_obj_tag(v___x_854_) == 0 {
                        v_a_855_ = leanh::lean_ctor_get(v___x_854_, 0);
                        leanh::lean_inc_n(v_a_855_, 2);
                        leanh::lean_dec_ref_known(v___x_854_, 1);
                        v___x_856_ =
                            l_Lean_Meta_getLevel(v_a_855_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                        if leanh::lean_obj_tag(v___x_856_) == 0 {
                            v_a_857_ = leanh::lean_ctor_get(v___x_856_, 0);
                            leanh::lean_inc(v_a_857_);
                            leanh::lean_dec_ref_known(v___x_856_, 1);
                            v___f_858_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                            leanh::lean_closure_set(v___f_858_, 0, v_i_843_);
                            leanh::lean_closure_set(v___f_858_, 1, v_insts_844_);
                            leanh::lean_closure_set(v___f_858_, 2, v_xs_841_);
                            leanh::lean_closure_set(v___f_858_, 3, v_k_842_);
                            v___x_859_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1;
                            v___x_860_ = leanh::lean_box(0);
                            v___x_861_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_861_, 0, v_a_857_);
                            leanh::lean_ctor_set(v___x_861_, 1, v___x_860_);
                            leanh::lean_inc_ref(v___x_861_);
                            v___x_862_ = l_Lean_Expr_const___override(v___x_859_, v___x_861_);
                            leanh::lean_inc(v_a_855_);
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
                            leanh::lean_dec(v_a_855_);
                            leanh::lean_dec(v_x_853_);
                            leanh::lean_dec_ref(v_insts_844_);
                            leanh::lean_dec(v_i_843_);
                            leanh::lean_dec_ref(v_k_842_);
                            leanh::lean_dec_ref(v_xs_841_);
                            v_a_871_ = leanh::lean_ctor_get(v___x_856_, 0);
                            v_isSharedCheck_878_ =
                                (!leanh::lean_is_exclusive(v___x_856_)) as u8;
                            if v_isSharedCheck_878_ == 0 {
                                v___x_873_ = v___x_856_;
                                v_isShared_874_ = v_isSharedCheck_878_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_871_);
                                leanh::lean_dec(v___x_856_);
                                v___x_873_ = leanh::lean_box(0);
                                v_isShared_874_ = v_isSharedCheck_878_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_853_);
                        leanh::lean_dec_ref(v_insts_844_);
                        leanh::lean_dec(v_i_843_);
                        leanh::lean_dec_ref(v_k_842_);
                        leanh::lean_dec_ref(v_xs_841_);
                        v_a_879_ = leanh::lean_ctor_get(v___x_854_, 0);
                        v_isSharedCheck_886_ = (!leanh::lean_is_exclusive(v___x_854_)) as u8;
                        if v_isSharedCheck_886_ == 0 {
                            v___x_881_ = v___x_854_;
                            v_isShared_882_ = v_isSharedCheck_886_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_879_);
                            leanh::lean_dec(v___x_854_);
                            v___x_881_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
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
                    v_reuseFailAlloc_885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
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
    mut v_i_887_: *mut leanh::LeanObject,
    mut v_insts_888_: *mut leanh::LeanObject,
    mut v_xs_889_: *mut leanh::LeanObject,
    mut v_k_890_: *mut leanh::LeanObject,
    mut v_inst_891_: *mut leanh::LeanObject,
    mut v___y_892_: *mut leanh::LeanObject,
    mut v___y_893_: *mut leanh::LeanObject,
    mut v___y_894_: *mut leanh::LeanObject,
    mut v___y_895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = leanh::lean_unsigned_to_nat(1);
    v___x_898_ = lean_nat_add(v_i_887_, v___x_897_);
    v___x_899_ = lean_array_push(v_insts_888_, v_inst_891_);
    v___x_900_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_889_, v_k_890_, v___x_898_, v___x_899_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
    return v___x_900_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(
    mut v_xs_901_: *mut leanh::LeanObject,
    mut v_k_902_: *mut leanh::LeanObject,
    mut v_i_903_: *mut leanh::LeanObject,
    mut v_insts_904_: *mut leanh::LeanObject,
    mut v_a_905_: *mut leanh::LeanObject,
    mut v_a_906_: *mut leanh::LeanObject,
    mut v_a_907_: *mut leanh::LeanObject,
    mut v_a_908_: *mut leanh::LeanObject,
    mut v_a_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_901_, v_k_902_, v_i_903_, v_insts_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
    leanh::lean_dec(v_a_908_);
    leanh::lean_dec_ref(v_a_907_);
    leanh::lean_dec(v_a_906_);
    leanh::lean_dec_ref(v_a_905_);
    return v_res_910_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(
    mut v_00_u03b1_911_: *mut leanh::LeanObject,
    mut v_xs_912_: *mut leanh::LeanObject,
    mut v_k_913_: *mut leanh::LeanObject,
    mut v_i_914_: *mut leanh::LeanObject,
    mut v_insts_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_912_, v_k_913_, v_i_914_, v_insts_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
    return v___x_921_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(
    mut v_00_u03b1_922_: *mut leanh::LeanObject,
    mut v_xs_923_: *mut leanh::LeanObject,
    mut v_k_924_: *mut leanh::LeanObject,
    mut v_i_925_: *mut leanh::LeanObject,
    mut v_insts_926_: *mut leanh::LeanObject,
    mut v_a_927_: *mut leanh::LeanObject,
    mut v_a_928_: *mut leanh::LeanObject,
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_932_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_930_);
    leanh::lean_dec_ref(v_a_929_);
    leanh::lean_dec(v_a_928_);
    leanh::lean_dec_ref(v_a_927_);
    return v_res_932_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(
    mut v_xs_935_: *mut leanh::LeanObject,
    mut v_k_936_: *mut leanh::LeanObject,
    mut v_a_937_: *mut leanh::LeanObject,
    mut v_a_938_: *mut leanh::LeanObject,
    mut v_a_939_: *mut leanh::LeanObject,
    mut v_a_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_942_ = leanh::lean_unsigned_to_nat(0);
    v___x_943_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0;
    v___x_944_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_935_, v_k_936_, v___x_942_, v___x_943_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
    return v___x_944_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(
    mut v_xs_945_: *mut leanh::LeanObject,
    mut v_k_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
    mut v_a_949_: *mut leanh::LeanObject,
    mut v_a_950_: *mut leanh::LeanObject,
    mut v_a_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_945_, v_k_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
    leanh::lean_dec(v_a_950_);
    leanh::lean_dec_ref(v_a_949_);
    leanh::lean_dec(v_a_948_);
    leanh::lean_dec_ref(v_a_947_);
    return v_res_952_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(
    mut v_00_u03b1_953_: *mut leanh::LeanObject,
    mut v_xs_954_: *mut leanh::LeanObject,
    mut v_k_955_: *mut leanh::LeanObject,
    mut v_a_956_: *mut leanh::LeanObject,
    mut v_a_957_: *mut leanh::LeanObject,
    mut v_a_958_: *mut leanh::LeanObject,
    mut v_a_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_961_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_954_, v_k_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
    return v___x_961_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(
    mut v_00_u03b1_962_: *mut leanh::LeanObject,
    mut v_xs_963_: *mut leanh::LeanObject,
    mut v_k_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
    mut v_a_966_: *mut leanh::LeanObject,
    mut v_a_967_: *mut leanh::LeanObject,
    mut v_a_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_970_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_968_);
    leanh::lean_dec_ref(v_a_967_);
    leanh::lean_dec(v_a_966_);
    leanh::lean_dec_ref(v_a_965_);
    return v_res_970_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
    mut v_type_971_: *mut leanh::LeanObject,
    mut v_useOfNonempty_972_: u8,
    mut v_a_973_: *mut leanh::LeanObject,
    mut v_a_974_: *mut leanh::LeanObject,
    mut v_a_975_: *mut leanh::LeanObject,
    mut v_a_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_980_: u8 = 0;
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u8 = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_992_: u8 = 0;
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_997_: u8 = 0;
    let mut v_a_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useOfNonempty_972_ == 0 {
                    v___x_988_ =
                        l_Lean_Meta_mkDefault(v_type_971_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
                    if leanh::lean_obj_tag(v___x_988_) == 0 {
                        v_a_989_ = leanh::lean_ctor_get(v___x_988_, 0);
                        v_isSharedCheck_997_ = (!leanh::lean_is_exclusive(v___x_988_)) as u8;
                        if v_isSharedCheck_997_ == 0 {
                            v___x_991_ = v___x_988_;
                            v_isShared_992_ = v_isSharedCheck_997_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_989_);
                            leanh::lean_dec(v___x_988_);
                            v___x_991_ = leanh::lean_box(0);
                            v_isShared_992_ = v_isSharedCheck_997_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_998_ = leanh::lean_ctor_get(v___x_988_, 0);
                        leanh::lean_inc(v_a_998_);
                        leanh::lean_dec_ref_known(v___x_988_, 1);
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
                    if leanh::lean_obj_tag(v___x_999_) == 0 {
                        v_a_1000_ = leanh::lean_ctor_get(v___x_999_, 0);
                        v_isSharedCheck_1008_ =
                            (!leanh::lean_is_exclusive(v___x_999_)) as u8;
                        if v_isSharedCheck_1008_ == 0 {
                            v___x_1002_ = v___x_999_;
                            v_isShared_1003_ = v_isSharedCheck_1008_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1000_);
                            leanh::lean_dec(v___x_999_);
                            v___x_1002_ = leanh::lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1008_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1009_ = leanh::lean_ctor_get(v___x_999_, 0);
                        leanh::lean_inc(v_a_1009_);
                        leanh::lean_dec_ref_known(v___x_999_, 1);
                        v_a_985_ = v_a_1009_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_980_ == 0 {
                    leanh::lean_dec_ref(v___y_979_);
                    v___x_981_ = leanh::lean_box(0);
                    v___x_982_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
                    return v___x_982_;
                } else {
                    v___x_983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_983_, 0, v___y_979_);
                    return v___x_983_;
                }
            }
            2 => {
                v___x_986_ = l_Lean_Exception_isInterrupt(v_a_985_);
                if v___x_986_ == 0 {
                    leanh::lean_inc_ref(v_a_985_);
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
                v___x_993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_993_, 0, v_a_989_);
                if v_isShared_992_ == 0 {
                    leanh::lean_ctor_set(v___x_991_, 0, v___x_993_);
                    v___x_995_ = v___x_991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_996_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
                    v___x_995_ = v_reuseFailAlloc_996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_995_;
            }
            5 => {
                v___x_1004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1004_, 0, v_a_1000_);
                if v_isShared_1003_ == 0 {
                    leanh::lean_ctor_set(v___x_1002_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
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
    mut v_type_1010_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1011_: *mut leanh::LeanObject,
    mut v_a_1012_: *mut leanh::LeanObject,
    mut v_a_1013_: *mut leanh::LeanObject,
    mut v_a_1014_: *mut leanh::LeanObject,
    mut v_a_1015_: *mut leanh::LeanObject,
    mut v_a_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1017_: u8 = 0;
    let mut v_res_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1017_ = (leanh::lean_unbox(v_useOfNonempty_1011_) as u8);
    v_res_1018_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
        v_type_1010_,
        v_useOfNonempty_boxed_1017_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
    );
    leanh::lean_dec(v_a_1015_);
    leanh::lean_dec_ref(v_a_1014_);
    leanh::lean_dec(v_a_1013_);
    leanh::lean_dec_ref(v_a_1012_);
    return v_res_1018_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(
    mut v_k_1019_: *mut leanh::LeanObject,
    mut v_b_1020_: *mut leanh::LeanObject,
    mut v_c_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
    mut v___y_1023_: *mut leanh::LeanObject,
    mut v___y_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1025_);
    leanh::lean_inc_ref(v___y_1024_);
    leanh::lean_inc(v___y_1023_);
    leanh::lean_inc_ref(v___y_1022_);
    v___x_1027_ = leanh::lean_apply_7(
        v_k_1019_,
        v_b_1020_,
        v_c_1021_,
        v___y_1022_,
        v___y_1023_,
        v___y_1024_,
        v___y_1025_,
        leanh::lean_box(0),
    );
    return v___x_1027_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(
    mut v_k_1028_: *mut leanh::LeanObject,
    mut v_b_1029_: *mut leanh::LeanObject,
    mut v_c_1030_: *mut leanh::LeanObject,
    mut v___y_1031_: *mut leanh::LeanObject,
    mut v___y_1032_: *mut leanh::LeanObject,
    mut v___y_1033_: *mut leanh::LeanObject,
    mut v___y_1034_: *mut leanh::LeanObject,
    mut v___y_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_1028_, v_b_1029_, v_c_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
    leanh::lean_dec(v___y_1034_);
    leanh::lean_dec_ref(v___y_1033_);
    leanh::lean_dec(v___y_1032_);
    leanh::lean_dec_ref(v___y_1031_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(
    mut v_type_1037_: *mut leanh::LeanObject,
    mut v_k_1038_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1039_: u8,
    mut v___y_1040_: *mut leanh::LeanObject,
    mut v___y_1041_: *mut leanh::LeanObject,
    mut v___y_1042_: *mut leanh::LeanObject,
    mut v___y_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1045_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1045_, 0, v_k_1038_);
                v___x_1046_ = 0;
                v___x_1047_ = leanh::lean_box(0);
                v___x_1048_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_1048_) == 0 {
                    v_a_1049_ = leanh::lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1056_ = (!leanh::lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1051_ = v___x_1048_;
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1049_);
                        leanh::lean_dec(v___x_1048_);
                        v___x_1051_ = leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1057_ = leanh::lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1064_ = (!leanh::lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1064_ == 0 {
                        v___x_1059_ = v___x_1048_;
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1057_);
                        leanh::lean_dec(v___x_1048_);
                        v___x_1059_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1055_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
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
                    v_reuseFailAlloc_1063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
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
    mut v_type_1065_: *mut leanh::LeanObject,
    mut v_k_1066_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1067_: *mut leanh::LeanObject,
    mut v___y_1068_: *mut leanh::LeanObject,
    mut v___y_1069_: *mut leanh::LeanObject,
    mut v___y_1070_: *mut leanh::LeanObject,
    mut v___y_1071_: *mut leanh::LeanObject,
    mut v___y_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1073_: u8 = 0;
    let mut v_res_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1073_ = (leanh::lean_unbox(v_cleanupAnnotations_1067_) as u8);
    v_res_1074_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_1065_, v_k_1066_, v_cleanupAnnotations_boxed_1073_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
    leanh::lean_dec(v___y_1071_);
    leanh::lean_dec_ref(v___y_1070_);
    leanh::lean_dec(v___y_1069_);
    leanh::lean_dec_ref(v___y_1068_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(
    mut v_00_u03b1_1075_: *mut leanh::LeanObject,
    mut v_type_1076_: *mut leanh::LeanObject,
    mut v_k_1077_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1078_: u8,
    mut v___y_1079_: *mut leanh::LeanObject,
    mut v___y_1080_: *mut leanh::LeanObject,
    mut v___y_1081_: *mut leanh::LeanObject,
    mut v___y_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_1076_, v_k_1077_, v_cleanupAnnotations_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
    return v___x_1084_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(
    mut v_00_u03b1_1085_: *mut leanh::LeanObject,
    mut v_type_1086_: *mut leanh::LeanObject,
    mut v_k_1087_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1094_: u8 = 0;
    let mut v_res_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1094_ = (leanh::lean_unbox(v_cleanupAnnotations_1088_) as u8);
    v_res_1095_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(v_00_u03b1_1085_, v_type_1086_, v_k_1087_, v_cleanupAnnotations_boxed_1094_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
    leanh::lean_dec(v___y_1092_);
    leanh::lean_dec_ref(v___y_1091_);
    leanh::lean_dec(v___y_1090_);
    leanh::lean_dec_ref(v___y_1089_);
    return v_res_1095_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1102_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1102_, 0, v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1103_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3);
    v___x_1104_ = l_Lean_MessageData_ofFormat(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4);
    v___x_1106_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2;
    v___x_1107_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    leanh::lean_ctor_set(v___x_1107_, 1, v___x_1105_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(
    mut v_ref_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5);
    v___x_1111_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1111_, 0, v_ref_1108_);
    leanh::lean_ctor_set(v___x_1111_, 1, v___x_1110_);
    v___x_1112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1112_, 0, v___x_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(
    mut v_ref_1113_: *mut leanh::LeanObject,
    mut v___y_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1113_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(
    mut v_00_u03b1_1116_: *mut leanh::LeanObject,
    mut v_ref_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1117_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(
    mut v_00_u03b1_1124_: *mut leanh::LeanObject,
    mut v_ref_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
    mut v___y_1129_: *mut leanh::LeanObject,
    mut v___y_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(v_00_u03b1_1124_, v_ref_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
    leanh::lean_dec(v___y_1129_);
    leanh::lean_dec_ref(v___y_1128_);
    leanh::lean_dec(v___y_1127_);
    leanh::lean_dec_ref(v___y_1126_);
    return v_res_1131_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(
    mut v_xs_1132_: *mut leanh::LeanObject,
    mut v_insts_1133_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1134_: *mut leanh::LeanObject,
    mut v_xs_x27_1135_: *mut leanh::LeanObject,
    mut v_type_x27_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1142_: u8 = 0;
    let mut v_res_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1142_ = (leanh::lean_unbox(v_useOfNonempty_1134_) as u8);
    v_res_1143_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_1132_, v_insts_1133_, v_useOfNonempty_boxed_1142_, v_xs_x27_1135_, v_type_x27_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
    leanh::lean_dec(v___y_1140_);
    leanh::lean_dec_ref(v___y_1139_);
    leanh::lean_dec(v___y_1138_);
    leanh::lean_dec_ref(v___y_1137_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(
    mut v_xs_1144_: *mut leanh::LeanObject,
    mut v_insts_1145_: *mut leanh::LeanObject,
    mut v_type_1146_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1147_: u8,
    mut v_a_1148_: *mut leanh::LeanObject,
    mut v_a_1149_: *mut leanh::LeanObject,
    mut v_a_1150_: *mut leanh::LeanObject,
    mut v_a_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1165_: u8 = 0;
    let mut v_cancelTk_x3f_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1167_: u8 = 0;
    let mut v_inheritedTraceOptions_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut v_a_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_a_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v_val_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: u8 = 0;
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1153_ = leanh::lean_ctor_get(v_a_1150_, 0);
                leanh::lean_inc_ref(v_fileName_1153_);
                v_fileMap_1154_ = leanh::lean_ctor_get(v_a_1150_, 1);
                leanh::lean_inc_ref(v_fileMap_1154_);
                v_options_1155_ = leanh::lean_ctor_get(v_a_1150_, 2);
                leanh::lean_inc_ref(v_options_1155_);
                v_currRecDepth_1156_ = leanh::lean_ctor_get(v_a_1150_, 3);
                leanh::lean_inc(v_currRecDepth_1156_);
                v_maxRecDepth_1157_ = leanh::lean_ctor_get(v_a_1150_, 4);
                leanh::lean_inc(v_maxRecDepth_1157_);
                v_ref_1158_ = leanh::lean_ctor_get(v_a_1150_, 5);
                leanh::lean_inc(v_ref_1158_);
                v_currNamespace_1159_ = leanh::lean_ctor_get(v_a_1150_, 6);
                leanh::lean_inc(v_currNamespace_1159_);
                v_openDecls_1160_ = leanh::lean_ctor_get(v_a_1150_, 7);
                leanh::lean_inc(v_openDecls_1160_);
                v_initHeartbeats_1161_ = leanh::lean_ctor_get(v_a_1150_, 8);
                leanh::lean_inc(v_initHeartbeats_1161_);
                v_maxHeartbeats_1162_ = leanh::lean_ctor_get(v_a_1150_, 9);
                leanh::lean_inc(v_maxHeartbeats_1162_);
                v_quotContext_1163_ = leanh::lean_ctor_get(v_a_1150_, 10);
                leanh::lean_inc(v_quotContext_1163_);
                v_currMacroScope_1164_ = leanh::lean_ctor_get(v_a_1150_, 11);
                leanh::lean_inc(v_currMacroScope_1164_);
                v_diag_1165_ = leanh::lean_ctor_get_uint8(
                    v_a_1150_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1166_ = leanh::lean_ctor_get(v_a_1150_, 12);
                leanh::lean_inc(v_cancelTk_x3f_1166_);
                v_suppressElabErrors_1167_ = leanh::lean_ctor_get_uint8(
                    v_a_1150_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1168_ = leanh::lean_ctor_get(v_a_1150_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_1168_);
                leanh::lean_dec_ref(v_a_1150_);
                v___x_1169_ = leanh::lean_box((v_useOfNonempty_1147_) as usize);
                leanh::lean_inc_ref(v_insts_1145_);
                leanh::lean_inc_ref(v_xs_1144_);
                v___f_1170_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_1170_, 0, v_xs_1144_);
                leanh::lean_closure_set(v___f_1170_, 1, v_insts_1145_);
                leanh::lean_closure_set(v___f_1170_, 2, v___x_1169_);
                v___x_1240_ = leanh::lean_unsigned_to_nat(0);
                v___x_1241_ = lean_nat_dec_eq(v_maxRecDepth_1157_, v___x_1240_);
                if v___x_1241_ == 0 {
                    v___x_1242_ = lean_nat_dec_eq(v_currRecDepth_1156_, v_maxRecDepth_1157_);
                    if v___x_1242_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___f_1170_);
                        leanh::lean_dec_ref(v_inheritedTraceOptions_1168_);
                        leanh::lean_dec(v_cancelTk_x3f_1166_);
                        leanh::lean_dec(v_currMacroScope_1164_);
                        leanh::lean_dec(v_quotContext_1163_);
                        leanh::lean_dec(v_maxHeartbeats_1162_);
                        leanh::lean_dec(v_initHeartbeats_1161_);
                        leanh::lean_dec(v_openDecls_1160_);
                        leanh::lean_dec(v_currNamespace_1159_);
                        leanh::lean_dec(v_maxRecDepth_1157_);
                        leanh::lean_dec(v_currRecDepth_1156_);
                        leanh::lean_dec_ref(v_options_1155_);
                        leanh::lean_dec_ref(v_fileMap_1154_);
                        leanh::lean_dec_ref(v_fileName_1153_);
                        leanh::lean_dec_ref(v_type_1146_);
                        leanh::lean_dec_ref(v_insts_1145_);
                        leanh::lean_dec_ref(v_xs_1144_);
                        v___x_1243_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1158_);
                        return v___x_1243_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1172_ = leanh::lean_unsigned_to_nat(1);
                v___x_1173_ = lean_nat_add(v_currRecDepth_1156_, v___x_1172_);
                leanh::lean_dec(v_currRecDepth_1156_);
                v___x_1174_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1174_, 0, v_fileName_1153_);
                leanh::lean_ctor_set(v___x_1174_, 1, v_fileMap_1154_);
                leanh::lean_ctor_set(v___x_1174_, 2, v_options_1155_);
                leanh::lean_ctor_set(v___x_1174_, 3, v___x_1173_);
                leanh::lean_ctor_set(v___x_1174_, 4, v_maxRecDepth_1157_);
                leanh::lean_ctor_set(v___x_1174_, 5, v_ref_1158_);
                leanh::lean_ctor_set(v___x_1174_, 6, v_currNamespace_1159_);
                leanh::lean_ctor_set(v___x_1174_, 7, v_openDecls_1160_);
                leanh::lean_ctor_set(v___x_1174_, 8, v_initHeartbeats_1161_);
                leanh::lean_ctor_set(v___x_1174_, 9, v_maxHeartbeats_1162_);
                leanh::lean_ctor_set(v___x_1174_, 10, v_quotContext_1163_);
                leanh::lean_ctor_set(v___x_1174_, 11, v_currMacroScope_1164_);
                leanh::lean_ctor_set(v___x_1174_, 12, v_cancelTk_x3f_1166_);
                leanh::lean_ctor_set(v___x_1174_, 13, v_inheritedTraceOptions_1168_);
                leanh::lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_1165_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1167_,
                );
                leanh::lean_inc_ref(v_type_1146_);
                v___x_1175_ =
                    l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
                        v_type_1146_,
                        v_useOfNonempty_1147_,
                        v_a_1148_,
                        v_a_1149_,
                        v___x_1174_,
                        v_a_1151_,
                    );
                if leanh::lean_obj_tag(v___x_1175_) == 0 {
                    v_a_1176_ = leanh::lean_ctor_get(v___x_1175_, 0);
                    leanh::lean_inc(v_a_1176_);
                    leanh::lean_dec_ref_known(v___x_1175_, 1);
                    if leanh::lean_obj_tag(v_a_1176_) == 1 {
                        leanh::lean_dec_ref(v___f_1170_);
                        leanh::lean_dec_ref(v_type_1146_);
                        v_val_1177_ = leanh::lean_ctor_get(v_a_1176_, 0);
                        v_isSharedCheck_1214_ = (!leanh::lean_is_exclusive(v_a_1176_)) as u8;
                        if v_isSharedCheck_1214_ == 0 {
                            v___x_1179_ = v_a_1176_;
                            v_isShared_1180_ = v_isSharedCheck_1214_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1177_);
                            leanh::lean_dec(v_a_1176_);
                            v___x_1179_ = leanh::lean_box(0);
                            v_isShared_1180_ = v_isSharedCheck_1214_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1176_);
                        v___x_1215_ = l_Lean_Meta_whnfCore(
                            v_type_1146_,
                            v_a_1148_,
                            v_a_1149_,
                            v___x_1174_,
                            v_a_1151_,
                        );
                        if leanh::lean_obj_tag(v___x_1215_) == 0 {
                            v_a_1216_ = leanh::lean_ctor_get(v___x_1215_, 0);
                            leanh::lean_inc(v_a_1216_);
                            leanh::lean_dec_ref_known(v___x_1215_, 1);
                            v___x_1217_ = l_Lean_Expr_isForall(v_a_1216_);
                            if v___x_1217_ == 0 {
                                leanh::lean_dec_ref(v___f_1170_);
                                v___x_1218_ = l_Lean_Meta_unfoldDefinition_x3f(
                                    v_a_1216_,
                                    v___x_1217_,
                                    v_a_1148_,
                                    v_a_1149_,
                                    v___x_1174_,
                                    v_a_1151_,
                                );
                                if leanh::lean_obj_tag(v___x_1218_) == 0 {
                                    v_a_1219_ = leanh::lean_ctor_get(v___x_1218_, 0);
                                    v_isSharedCheck_1229_ =
                                        (!leanh::lean_is_exclusive(v___x_1218_)) as u8;
                                    if v_isSharedCheck_1229_ == 0 {
                                        v___x_1221_ = v___x_1218_;
                                        v_isShared_1222_ = v_isSharedCheck_1229_;
                                        state = 10;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1219_);
                                        leanh::lean_dec(v___x_1218_);
                                        v___x_1221_ = leanh::lean_box(0);
                                        v_isShared_1222_ = v_isSharedCheck_1229_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v___x_1174_, 14);
                                    leanh::lean_dec_ref(v_insts_1145_);
                                    leanh::lean_dec_ref(v_xs_1144_);
                                    return v___x_1218_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_insts_1145_);
                                leanh::lean_dec_ref(v_xs_1144_);
                                v___x_1230_ = 0;
                                v___x_1231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_a_1216_, v___f_1170_, v___x_1230_, v_a_1148_, v_a_1149_, v___x_1174_, v_a_1151_);
                                leanh::lean_dec_ref_known(v___x_1174_, 14);
                                return v___x_1231_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_1174_, 14);
                            leanh::lean_dec_ref(v___f_1170_);
                            leanh::lean_dec_ref(v_insts_1145_);
                            leanh::lean_dec_ref(v_xs_1144_);
                            v_a_1232_ = leanh::lean_ctor_get(v___x_1215_, 0);
                            v_isSharedCheck_1239_ =
                                (!leanh::lean_is_exclusive(v___x_1215_)) as u8;
                            if v_isSharedCheck_1239_ == 0 {
                                v___x_1234_ = v___x_1215_;
                                v_isShared_1235_ = v_isSharedCheck_1239_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1232_);
                                leanh::lean_dec(v___x_1215_);
                                v___x_1234_ = leanh::lean_box(0);
                                v_isShared_1235_ = v_isSharedCheck_1239_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_1174_, 14);
                    leanh::lean_dec_ref(v___f_1170_);
                    leanh::lean_dec_ref(v_type_1146_);
                    leanh::lean_dec_ref(v_insts_1145_);
                    leanh::lean_dec_ref(v_xs_1144_);
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
                leanh::lean_dec_ref(v_insts_1145_);
                if leanh::lean_obj_tag(v___x_1183_) == 0 {
                    v_a_1184_ = leanh::lean_ctor_get(v___x_1183_, 0);
                    leanh::lean_inc(v_a_1184_);
                    leanh::lean_dec_ref_known(v___x_1183_, 1);
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
                    leanh::lean_dec_ref_known(v___x_1174_, 14);
                    leanh::lean_dec_ref(v_xs_1144_);
                    if leanh::lean_obj_tag(v___x_1186_) == 0 {
                        v_a_1187_ = leanh::lean_ctor_get(v___x_1186_, 0);
                        v_isSharedCheck_1197_ =
                            (!leanh::lean_is_exclusive(v___x_1186_)) as u8;
                        if v_isSharedCheck_1197_ == 0 {
                            v___x_1189_ = v___x_1186_;
                            v_isShared_1190_ = v_isSharedCheck_1197_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1187_);
                            leanh::lean_dec(v___x_1186_);
                            v___x_1189_ = leanh::lean_box(0);
                            v_isShared_1190_ = v_isSharedCheck_1197_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1179_);
                        v_a_1198_ = leanh::lean_ctor_get(v___x_1186_, 0);
                        v_isSharedCheck_1205_ =
                            (!leanh::lean_is_exclusive(v___x_1186_)) as u8;
                        if v_isSharedCheck_1205_ == 0 {
                            v___x_1200_ = v___x_1186_;
                            v_isShared_1201_ = v_isSharedCheck_1205_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1198_);
                            leanh::lean_dec(v___x_1186_);
                            v___x_1200_ = leanh::lean_box(0);
                            v_isShared_1201_ = v_isSharedCheck_1205_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1179_);
                    leanh::lean_dec_ref_known(v___x_1174_, 14);
                    leanh::lean_dec_ref(v_xs_1144_);
                    v_a_1206_ = leanh::lean_ctor_get(v___x_1183_, 0);
                    v_isSharedCheck_1213_ = (!leanh::lean_is_exclusive(v___x_1183_)) as u8;
                    if v_isSharedCheck_1213_ == 0 {
                        v___x_1208_ = v___x_1183_;
                        v_isShared_1209_ = v_isSharedCheck_1213_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1206_);
                        leanh::lean_dec(v___x_1183_);
                        v___x_1208_ = leanh::lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1213_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1180_ == 0 {
                    leanh::lean_ctor_set(v___x_1179_, 0, v_a_1187_);
                    v___x_1192_ = v___x_1179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1187_);
                    v___x_1192_ = v_reuseFailAlloc_1196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1190_ == 0 {
                    leanh::lean_ctor_set(v___x_1189_, 0, v___x_1192_);
                    v___x_1194_ = v___x_1189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
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
                    v_reuseFailAlloc_1204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
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
                    v_reuseFailAlloc_1212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1211_;
            }
            10 => {
                if leanh::lean_obj_tag(v_a_1219_) == 1 {
                    leanh::lean_del_object(v___x_1221_);
                    v_val_1223_ = leanh::lean_ctor_get(v_a_1219_, 0);
                    leanh::lean_inc(v_val_1223_);
                    leanh::lean_dec_ref_known(v_a_1219_, 1);
                    v_type_1146_ = v_val_1223_;
                    v_a_1150_ = v___x_1174_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_1219_);
                    leanh::lean_dec_ref_known(v___x_1174_, 14);
                    leanh::lean_dec_ref(v_insts_1145_);
                    leanh::lean_dec_ref(v_xs_1144_);
                    v___x_1225_ = leanh::lean_box(0);
                    if v_isShared_1222_ == 0 {
                        leanh::lean_ctor_set(v___x_1221_, 0, v___x_1225_);
                        v___x_1227_ = v___x_1221_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
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
                    v_reuseFailAlloc_1238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
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
    mut v_xs_1244_: *mut leanh::LeanObject,
    mut v_xs_x27_1245_: *mut leanh::LeanObject,
    mut v_insts_1246_: *mut leanh::LeanObject,
    mut v_type_x27_1247_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1248_: u8,
    mut v_insts_x27_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
    mut v___y_1251_: *mut leanh::LeanObject,
    mut v___y_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Array_append___redArg(v_xs_1244_, v_xs_x27_1245_);
    v___x_1256_ = l_Array_append___redArg(v_insts_1246_, v_insts_x27_1249_);
    leanh::lean_inc_ref(v___y_1252_);
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
    mut v_xs_1258_: *mut leanh::LeanObject,
    mut v_xs_x27_1259_: *mut leanh::LeanObject,
    mut v_insts_1260_: *mut leanh::LeanObject,
    mut v_type_x27_1261_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1262_: *mut leanh::LeanObject,
    mut v_insts_x27_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1269_: u8 = 0;
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1269_ = (leanh::lean_unbox(v_useOfNonempty_1262_) as u8);
    v_res_1270_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_1258_, v_xs_x27_1259_, v_insts_1260_, v_type_x27_1261_, v_useOfNonempty_boxed_1269_, v_insts_x27_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    leanh::lean_dec(v___y_1267_);
    leanh::lean_dec_ref(v___y_1266_);
    leanh::lean_dec(v___y_1265_);
    leanh::lean_dec_ref(v___y_1264_);
    leanh::lean_dec_ref(v_insts_x27_1263_);
    leanh::lean_dec_ref(v_xs_x27_1259_);
    return v_res_1270_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(
    mut v_xs_1271_: *mut leanh::LeanObject,
    mut v_insts_1272_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1273_: u8,
    mut v_xs_x27_1274_: *mut leanh::LeanObject,
    mut v_type_x27_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = leanh::lean_box((v_useOfNonempty_1273_) as usize);
    leanh::lean_inc_ref(v_xs_x27_1274_);
    v___f_1282_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
    leanh::lean_closure_set(v___f_1282_, 0, v_xs_1271_);
    leanh::lean_closure_set(v___f_1282_, 1, v_xs_x27_1274_);
    leanh::lean_closure_set(v___f_1282_, 2, v_insts_1272_);
    leanh::lean_closure_set(v___f_1282_, 3, v_type_x27_1275_);
    leanh::lean_closure_set(v___f_1282_, 4, v___x_1281_);
    v___x_1283_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_x27_1274_, v___f_1282_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
    return v___x_1283_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(
    mut v_xs_1284_: *mut leanh::LeanObject,
    mut v_insts_1285_: *mut leanh::LeanObject,
    mut v_type_1286_: *mut leanh::LeanObject,
    mut v_useOfNonempty_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useOfNonempty_boxed_1293_: u8 = 0;
    let mut v_res_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1293_ = (leanh::lean_unbox(v_useOfNonempty_1287_) as u8);
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
    leanh::lean_dec(v_a_1291_);
    leanh::lean_dec(v_a_1289_);
    leanh::lean_dec_ref(v_a_1288_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(
    mut v_msgData_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1301_ = lean_st_ref_get(v___y_1299_);
    v_env_1302_ = leanh::lean_ctor_get(v___x_1301_, 0);
    leanh::lean_inc_ref(v_env_1302_);
    leanh::lean_dec(v___x_1301_);
    v___x_1303_ = lean_st_ref_get(v___y_1297_);
    v_mctx_1304_ = leanh::lean_ctor_get(v___x_1303_, 0);
    leanh::lean_inc_ref(v_mctx_1304_);
    leanh::lean_dec(v___x_1303_);
    v_lctx_1305_ = leanh::lean_ctor_get(v___y_1296_, 2);
    v_options_1306_ = leanh::lean_ctor_get(v___y_1298_, 2);
    leanh::lean_inc_ref(v_options_1306_);
    leanh::lean_inc_ref(v_lctx_1305_);
    v___x_1307_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1307_, 0, v_env_1302_);
    leanh::lean_ctor_set(v___x_1307_, 1, v_mctx_1304_);
    leanh::lean_ctor_set(v___x_1307_, 2, v_lctx_1305_);
    leanh::lean_ctor_set(v___x_1307_, 3, v_options_1306_);
    v___x_1308_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1308_, 0, v___x_1307_);
    leanh::lean_ctor_set(v___x_1308_, 1, v_msgData_1295_);
    v___x_1309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1309_, 0, v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(
    mut v_msgData_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
    mut v___y_1313_: *mut leanh::LeanObject,
    mut v___y_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
    leanh::lean_dec(v___y_1314_);
    leanh::lean_dec_ref(v___y_1313_);
    leanh::lean_dec(v___y_1312_);
    leanh::lean_dec_ref(v___y_1311_);
    return v_res_1316_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
    mut v_msg_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1323_ = leanh::lean_ctor_get(v___y_1320_, 5);
                v___x_1324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
                v_a_1325_ = leanh::lean_ctor_get(v___x_1324_, 0);
                v_isSharedCheck_1333_ = (!leanh::lean_is_exclusive(v___x_1324_)) as u8;
                if v_isSharedCheck_1333_ == 0 {
                    v___x_1327_ = v___x_1324_;
                    v_isShared_1328_ = v_isSharedCheck_1333_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1325_);
                    leanh::lean_dec(v___x_1324_);
                    v___x_1327_ = leanh::lean_box(0);
                    v_isShared_1328_ = v_isSharedCheck_1333_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1323_);
                v___x_1329_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1329_, 0, v_ref_1323_);
                leanh::lean_ctor_set(v___x_1329_, 1, v_a_1325_);
                if v_isShared_1328_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1327_, 1);
                    leanh::lean_ctor_set(v___x_1327_, 0, v___x_1329_);
                    v___x_1331_ = v___x_1327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
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
    mut v_msg_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
    mut v___y_1337_: *mut leanh::LeanObject,
    mut v___y_1338_: *mut leanh::LeanObject,
    mut v___y_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
        v_msg_1334_,
        v___y_1335_,
        v___y_1336_,
        v___y_1337_,
        v___y_1338_,
    );
    leanh::lean_dec(v___y_1338_);
    leanh::lean_dec_ref(v___y_1337_);
    leanh::lean_dec(v___y_1336_);
    leanh::lean_dec_ref(v___y_1335_);
    return v_res_1340_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__0;
    v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__2;
    v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = 0;
    v___x_1348_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1;
    v___x_1349_ = l_Lean_MessageData_ofConstName(v___x_1348_, v___x_1347_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__5;
    v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = 0;
    v___x_1357_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__8;
    v___x_1358_ = l_Lean_MessageData_ofConstName(v___x_1357_, v___x_1356_);
    return v___x_1358_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__10;
    v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__12;
    v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___lam__0(
    mut v_xs_1365_: *mut leanh::LeanObject,
    mut v_type_1366_: *mut leanh::LeanObject,
    mut v_failedToMessage_1367_: *mut leanh::LeanObject,
    mut v_insts_1368_: *mut leanh::LeanObject,
    mut v___y_1369_: *mut leanh::LeanObject,
    mut v___y_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
    mut v___y_1372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1374_: u8 = 0;
    let mut v___y_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v_val_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_a_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1374_ = 0;
                leanh::lean_inc_ref(v___y_1371_);
                leanh::lean_inc_ref(v_type_1366_);
                leanh::lean_inc_ref(v_insts_1368_);
                leanh::lean_inc_ref(v_xs_1365_);
                v___x_1416_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_1365_, v_insts_1368_, v_type_1366_, v___x_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                if leanh::lean_obj_tag(v___x_1416_) == 0 {
                    v_a_1417_ = leanh::lean_ctor_get(v___x_1416_, 0);
                    leanh::lean_inc(v_a_1417_);
                    if leanh::lean_obj_tag(v_a_1417_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1416_, 1);
                        v___x_1418_ = 1;
                        leanh::lean_inc_ref(v___y_1371_);
                        leanh::lean_inc_ref(v_type_1366_);
                        leanh::lean_inc_ref(v_xs_1365_);
                        v___x_1419_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_1365_, v_insts_1368_, v_type_1366_, v___x_1418_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                        v___y_1376_ = v___x_1419_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_a_1417_, 1);
                        leanh::lean_dec_ref(v_insts_1368_);
                        v___y_1376_ = v___x_1416_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_insts_1368_);
                    v___y_1376_ = v___x_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1376_) == 0 {
                    v_a_1377_ = leanh::lean_ctor_get(v___y_1376_, 0);
                    v_isSharedCheck_1407_ = (!leanh::lean_is_exclusive(v___y_1376_)) as u8;
                    if v_isSharedCheck_1407_ == 0 {
                        v___x_1379_ = v___y_1376_;
                        v_isShared_1380_ = v_isSharedCheck_1407_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1377_);
                        leanh::lean_dec(v___y_1376_);
                        v___x_1379_ = leanh::lean_box(0);
                        v_isShared_1380_ = v_isSharedCheck_1407_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_failedToMessage_1367_);
                    leanh::lean_dec_ref(v_type_1366_);
                    leanh::lean_dec_ref(v_xs_1365_);
                    v_a_1408_ = leanh::lean_ctor_get(v___y_1376_, 0);
                    v_isSharedCheck_1415_ = (!leanh::lean_is_exclusive(v___y_1376_)) as u8;
                    if v_isSharedCheck_1415_ == 0 {
                        v___x_1410_ = v___y_1376_;
                        v_isShared_1411_ = v_isSharedCheck_1415_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1408_);
                        leanh::lean_dec(v___y_1376_);
                        v___x_1410_ = leanh::lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1415_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_1377_) == 1 {
                    leanh::lean_dec_ref(v_failedToMessage_1367_);
                    leanh::lean_dec_ref(v_type_1366_);
                    leanh::lean_dec_ref(v_xs_1365_);
                    v_val_1381_ = leanh::lean_ctor_get(v_a_1377_, 0);
                    leanh::lean_inc(v_val_1381_);
                    leanh::lean_dec_ref_known(v_a_1377_, 1);
                    if v_isShared_1380_ == 0 {
                        leanh::lean_ctor_set(v___x_1379_, 0, v_val_1381_);
                        v___x_1383_ = v___x_1379_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1384_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_val_1381_);
                        v___x_1383_ = v_reuseFailAlloc_1384_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1379_);
                    leanh::lean_dec(v_a_1377_);
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
                    leanh::lean_dec_ref(v_xs_1365_);
                    if leanh::lean_obj_tag(v___x_1387_) == 0 {
                        v_a_1388_ = leanh::lean_ctor_get(v___x_1387_, 0);
                        leanh::lean_inc(v_a_1388_);
                        leanh::lean_dec_ref_known(v___x_1387_, 1);
                        v___x_1389_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1,
                        );
                        v___x_1390_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1390_, 0, v_failedToMessage_1367_);
                        leanh::lean_ctor_set(v___x_1390_, 1, v___x_1389_);
                        v___x_1391_ = l_Lean_indentExpr(v_a_1388_);
                        v___x_1392_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1392_, 0, v___x_1390_);
                        leanh::lean_ctor_set(v___x_1392_, 1, v___x_1391_);
                        v___x_1393_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3,
                        );
                        v___x_1394_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1394_, 0, v___x_1392_);
                        leanh::lean_ctor_set(v___x_1394_, 1, v___x_1393_);
                        v___x_1395_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4,
                        );
                        v___x_1396_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1396_, 0, v___x_1394_);
                        leanh::lean_ctor_set(v___x_1396_, 1, v___x_1395_);
                        v___x_1397_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6,
                        );
                        v___x_1398_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1398_, 0, v___x_1396_);
                        leanh::lean_ctor_set(v___x_1398_, 1, v___x_1397_);
                        v___x_1399_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9,
                        );
                        v___x_1400_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1400_, 0, v___x_1398_);
                        leanh::lean_ctor_set(v___x_1400_, 1, v___x_1399_);
                        v___x_1401_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11,
                        );
                        v___x_1402_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1402_, 0, v___x_1400_);
                        leanh::lean_ctor_set(v___x_1402_, 1, v___x_1401_);
                        v___x_1403_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1403_, 0, v___x_1402_);
                        leanh::lean_ctor_set(v___x_1403_, 1, v___x_1395_);
                        v___x_1404_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13,
                        );
                        v___x_1405_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1405_, 0, v___x_1403_);
                        leanh::lean_ctor_set(v___x_1405_, 1, v___x_1404_);
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
                        leanh::lean_dec_ref(v_failedToMessage_1367_);
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
                    v_reuseFailAlloc_1414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
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
    mut v_xs_1420_: *mut leanh::LeanObject,
    mut v_type_1421_: *mut leanh::LeanObject,
    mut v_failedToMessage_1422_: *mut leanh::LeanObject,
    mut v_insts_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___y_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1427_);
    leanh::lean_dec_ref(v___y_1426_);
    leanh::lean_dec(v___y_1425_);
    leanh::lean_dec_ref(v___y_1424_);
    return v_res_1429_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor(
    mut v_failedToMessage_1430_: *mut leanh::LeanObject,
    mut v_xs_1431_: *mut leanh::LeanObject,
    mut v_type_1432_: *mut leanh::LeanObject,
    mut v_a_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
    mut v_a_1435_: *mut leanh::LeanObject,
    mut v_a_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_xs_1431_);
    v___f_1438_ = leanh::lean_alloc_closure(
        l_Lean_Elab_mkInhabitantFor___lam__0___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    leanh::lean_closure_set(v___f_1438_, 0, v_xs_1431_);
    leanh::lean_closure_set(v___f_1438_, 1, v_type_1432_);
    leanh::lean_closure_set(v___f_1438_, 2, v_failedToMessage_1430_);
    v___x_1439_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_1431_, v___f_1438_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___boxed(
    mut v_failedToMessage_1440_: *mut leanh::LeanObject,
    mut v_xs_1441_: *mut leanh::LeanObject,
    mut v_type_1442_: *mut leanh::LeanObject,
    mut v_a_1443_: *mut leanh::LeanObject,
    mut v_a_1444_: *mut leanh::LeanObject,
    mut v_a_1445_: *mut leanh::LeanObject,
    mut v_a_1446_: *mut leanh::LeanObject,
    mut v_a_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1448_ = l_Lean_Elab_mkInhabitantFor(
        v_failedToMessage_1440_,
        v_xs_1441_,
        v_type_1442_,
        v_a_1443_,
        v_a_1444_,
        v_a_1445_,
        v_a_1446_,
    );
    leanh::lean_dec(v_a_1446_);
    leanh::lean_dec_ref(v_a_1445_);
    leanh::lean_dec(v_a_1444_);
    leanh::lean_dec_ref(v_a_1443_);
    return v_res_1448_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(
    mut v_00_u03b1_1449_: *mut leanh::LeanObject,
    mut v_msg_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1457_: *mut leanh::LeanObject,
    mut v_msg_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(
        v_00_u03b1_1457_,
        v_msg_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
    );
    leanh::lean_dec(v___y_1462_);
    leanh::lean_dec_ref(v___y_1461_);
    leanh::lean_dec(v___y_1460_);
    leanh::lean_dec_ref(v___y_1459_);
    return v_res_1464_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_MkInhabitant(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
}