// Lean compiler output
// Module: Lean.Elab.PreDefinition.MkInhabitant
// Imports: Lean.Meta.AppBuilder Lean.PrettyPrinter Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage,
};
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut LeanObject,13340093926952294564 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value) as *mut LeanObject,13340093926952294564 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value) as *mut LeanObject,17998702798483655788 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value) as *mut LeanObject,6605161548626312362 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            44, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 112, 114, 111, 118, 101, 32,
            116, 104, 97, 116, 32, 116, 104, 101, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value: LeanStringObject<137> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 137,
        m_capacity: 137,
        m_length: 136,
        m_data: [
            10, 105, 115, 32, 110, 111, 110, 101, 109, 112, 116, 121, 46, 10, 10, 84, 104, 105,
            115, 32, 112, 114, 111, 99, 101, 115, 115, 32, 117, 115, 101, 115, 32, 109, 117, 108,
            116, 105, 112, 108, 101, 32, 115, 116, 114, 97, 116, 101, 103, 105, 101, 115, 58, 10,
            45, 32, 73, 116, 32, 108, 111, 111, 107, 115, 32, 102, 111, 114, 32, 97, 32, 112, 97,
            114, 97, 109, 101, 116, 101, 114, 32, 116, 104, 97, 116, 32, 109, 97, 116, 99, 104,
            101, 115, 32, 116, 104, 101, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101,
            46, 10, 45, 32, 73, 116, 32, 116, 114, 105, 101, 115, 32, 115, 121, 110, 116, 104, 101,
            115, 105, 122, 105, 110, 103, 32, 39, 0,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value) as *mut LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value)
                as *mut LeanObject,
            13229434762204987278 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value) as *mut LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value: LeanStringObject<77> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 77,
        m_capacity: 77,
        m_length: 76,
        m_data: [
            39, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 102, 111, 114, 32, 116, 104,
            101, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 44, 32, 119, 104, 105,
            108, 101, 32, 109, 97, 107, 105, 110, 103, 32, 101, 118, 101, 114, 121, 32, 112, 97,
            114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 116, 111, 32, 97, 32, 108, 111, 99, 97,
            108, 32, 39, 0,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value) as *mut LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value: LeanStringObject<182> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 182,
        m_capacity: 182,
        m_length: 181,
        m_data: [
            39, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 10, 45, 32, 73, 116, 32, 116, 114,
            105, 101, 115, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 116, 104, 101, 32,
            114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 46, 10, 10, 73, 102, 32, 116,
            104, 101, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 32, 105, 115, 32,
            100, 101, 102, 105, 110, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32,
            39, 115, 116, 114, 117, 99, 116, 117, 114, 101, 39, 32, 111, 114, 32, 39, 105, 110,
            100, 117, 99, 116, 105, 118, 101, 39, 32, 99, 111, 109, 109, 97, 110, 100, 44, 32, 121,
            111, 117, 32, 99, 97, 110, 32, 116, 114, 121, 32, 97, 100, 100, 105, 110, 103, 32, 97,
            32, 39, 100, 101, 114, 105, 118, 105, 110, 103, 32, 78, 111, 110, 101, 109, 112, 116,
            121, 39, 32, 99, 108, 97, 117, 115, 101, 32, 116, 111, 32, 105, 116, 46, 0,
        ],
    };
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value) as *mut LeanObject;
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkInhabitantFor___lam__0___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(
    mut v_k_733_: *mut LeanObject,
    mut v_b_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_738_);
    lean_inc_ref(v___y_737_);
    lean_inc(v___y_736_);
    lean_inc_ref(v___y_735_);
    v___x_740_ = lean_apply_6(
        v_k_733_,
        v_b_734_,
        v___y_735_,
        v___y_736_,
        v___y_737_,
        v___y_738_,
        lean_box(0),
    );
    return v___x_740_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(
    mut v_k_741_: *mut LeanObject,
    mut v_b_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_748_: *mut LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_741_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
    lean_dec(v___y_746_);
    lean_dec_ref(v___y_745_);
    lean_dec(v___y_744_);
    lean_dec_ref(v___y_743_);
    return v_res_748_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(
    mut v_name_749_: *mut LeanObject,
    mut v_type_750_: *mut LeanObject,
    mut v_val_751_: *mut LeanObject,
    mut v_k_752_: *mut LeanObject,
    mut v_nondep_753_: u8,
    mut v_kind_754_: u8,
    mut v___y_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
    mut v___y_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_765_: u8 = 0;
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_a_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_760_ = lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_760_, 0, v_k_752_);
                v___x_761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_761_) == 0 {
                    v_a_762_ = lean_ctor_get(v___x_761_, 0);
                    v_isSharedCheck_769_ = (!lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_769_ == 0 {
                        v___x_764_ = v___x_761_;
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_762_);
                        lean_dec(v___x_761_);
                        v___x_764_ = lean_box(0);
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_770_ = lean_ctor_get(v___x_761_, 0);
                    v_isSharedCheck_777_ = (!lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_777_ == 0 {
                        v___x_772_ = v___x_761_;
                        v_isShared_773_ = v_isSharedCheck_777_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_770_);
                        lean_dec(v___x_761_);
                        v___x_772_ = lean_box(0);
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
                    v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
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
                    v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
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
    mut v_name_778_: *mut LeanObject,
    mut v_type_779_: *mut LeanObject,
    mut v_val_780_: *mut LeanObject,
    mut v_k_781_: *mut LeanObject,
    mut v_nondep_782_: *mut LeanObject,
    mut v_kind_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_789_: u8 = 0;
    let mut v_kind_boxed_790_: u8 = 0;
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_789_ = (lean_unbox(v_nondep_782_) as u8);
    v_kind_boxed_790_ = (lean_unbox(v_kind_783_) as u8);
    v_res_791_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_778_, v_type_779_, v_val_780_, v_k_781_, v_nondep_boxed_789_, v_kind_boxed_790_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
    lean_dec(v___y_787_);
    lean_dec_ref(v___y_786_);
    lean_dec(v___y_785_);
    lean_dec_ref(v___y_784_);
    return v_res_791_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(
    mut v_00_u03b1_792_: *mut LeanObject,
    mut v_name_793_: *mut LeanObject,
    mut v_type_794_: *mut LeanObject,
    mut v_val_795_: *mut LeanObject,
    mut v_k_796_: *mut LeanObject,
    mut v_nondep_797_: u8,
    mut v_kind_798_: u8,
    mut v___y_799_: *mut LeanObject,
    mut v___y_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
    mut v___y_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_793_, v_type_794_, v_val_795_, v_k_796_, v_nondep_797_, v_kind_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
    return v___x_804_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(
    mut v_00_u03b1_805_: *mut LeanObject,
    mut v_name_806_: *mut LeanObject,
    mut v_type_807_: *mut LeanObject,
    mut v_val_808_: *mut LeanObject,
    mut v_k_809_: *mut LeanObject,
    mut v_nondep_810_: *mut LeanObject,
    mut v_kind_811_: *mut LeanObject,
    mut v___y_812_: *mut LeanObject,
    mut v___y_813_: *mut LeanObject,
    mut v___y_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_817_: u8 = 0;
    let mut v_kind_boxed_818_: u8 = 0;
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_817_ = (lean_unbox(v_nondep_810_) as u8);
    v_kind_boxed_818_ = (lean_unbox(v_kind_811_) as u8);
    v_res_819_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(v_00_u03b1_805_, v_name_806_, v_type_807_, v_val_808_, v_k_809_, v_nondep_boxed_817_, v_kind_boxed_818_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
    lean_dec(v___y_815_);
    lean_dec_ref(v___y_814_);
    lean_dec(v___y_813_);
    lean_dec_ref(v___y_812_);
    return v_res_819_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(
    mut v_i_820_: *mut LeanObject,
    mut v_insts_821_: *mut LeanObject,
    mut v_xs_822_: *mut LeanObject,
    mut v_k_823_: *mut LeanObject,
    mut v_inst_824_: *mut LeanObject,
    mut v___y_825_: *mut LeanObject,
    mut v___y_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
    mut v___y_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_820_, v_insts_821_, v_xs_822_, v_k_823_, v_inst_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
    lean_dec(v___y_828_);
    lean_dec_ref(v___y_827_);
    lean_dec(v___y_826_);
    lean_dec_ref(v___y_825_);
    lean_dec(v_i_820_);
    return v_res_830_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(
    mut v_xs_841_: *mut LeanObject,
    mut v_k_842_: *mut LeanObject,
    mut v_i_843_: *mut LeanObject,
    mut v_insts_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_a_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_878_: u8 = 0;
    let mut v_a_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_850_ = lean_array_get_size(v_xs_841_);
                v___x_851_ = lean_nat_dec_lt(v_i_843_, v___x_850_);
                if v___x_851_ == 0 {
                    lean_dec(v_i_843_);
                    lean_dec_ref(v_xs_841_);
                    lean_inc(v_a_848_);
                    lean_inc_ref(v_a_847_);
                    lean_inc(v_a_846_);
                    lean_inc_ref(v_a_845_);
                    v___x_852_ = lean_apply_6(
                        v_k_842_,
                        v_insts_844_,
                        v_a_845_,
                        v_a_846_,
                        v_a_847_,
                        v_a_848_,
                        lean_box(0),
                    );
                    return v___x_852_;
                } else {
                    v_x_853_ = lean_array_fget(v_xs_841_, v_i_843_);
                    lean_inc(v_a_848_);
                    lean_inc_ref(v_a_847_);
                    lean_inc(v_a_846_);
                    lean_inc_ref(v_a_845_);
                    lean_inc(v_x_853_);
                    v___x_854_ = lean_infer_type(v_x_853_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                    if lean_obj_tag(v___x_854_) == 0 {
                        v_a_855_ = lean_ctor_get(v___x_854_, 0);
                        lean_inc_n(v_a_855_, 2);
                        lean_dec_ref_known(v___x_854_, 1);
                        v___x_856_ =
                            l_Lean_Meta_getLevel(v_a_855_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
                        if lean_obj_tag(v___x_856_) == 0 {
                            v_a_857_ = lean_ctor_get(v___x_856_, 0);
                            lean_inc(v_a_857_);
                            lean_dec_ref_known(v___x_856_, 1);
                            v___f_858_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                            lean_closure_set(v___f_858_, 0, v_i_843_);
                            lean_closure_set(v___f_858_, 1, v_insts_844_);
                            lean_closure_set(v___f_858_, 2, v_xs_841_);
                            lean_closure_set(v___f_858_, 3, v_k_842_);
                            v___x_859_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1;
                            v___x_860_ = lean_box(0);
                            v___x_861_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_861_, 0, v_a_857_);
                            lean_ctor_set(v___x_861_, 1, v___x_860_);
                            lean_inc_ref(v___x_861_);
                            v___x_862_ = l_Lean_Expr_const___override(v___x_859_, v___x_861_);
                            lean_inc(v_a_855_);
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
                            lean_dec(v_a_855_);
                            lean_dec(v_x_853_);
                            lean_dec_ref(v_insts_844_);
                            lean_dec(v_i_843_);
                            lean_dec_ref(v_k_842_);
                            lean_dec_ref(v_xs_841_);
                            v_a_871_ = lean_ctor_get(v___x_856_, 0);
                            v_isSharedCheck_878_ = (!lean_is_exclusive(v___x_856_)) as u8;
                            if v_isSharedCheck_878_ == 0 {
                                v___x_873_ = v___x_856_;
                                v_isShared_874_ = v_isSharedCheck_878_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_871_);
                                lean_dec(v___x_856_);
                                v___x_873_ = lean_box(0);
                                v_isShared_874_ = v_isSharedCheck_878_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_x_853_);
                        lean_dec_ref(v_insts_844_);
                        lean_dec(v_i_843_);
                        lean_dec_ref(v_k_842_);
                        lean_dec_ref(v_xs_841_);
                        v_a_879_ = lean_ctor_get(v___x_854_, 0);
                        v_isSharedCheck_886_ = (!lean_is_exclusive(v___x_854_)) as u8;
                        if v_isSharedCheck_886_ == 0 {
                            v___x_881_ = v___x_854_;
                            v_isShared_882_ = v_isSharedCheck_886_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_879_);
                            lean_dec(v___x_854_);
                            v___x_881_ = lean_box(0);
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
                    v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
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
                    v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
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
    mut v_i_887_: *mut LeanObject,
    mut v_insts_888_: *mut LeanObject,
    mut v_xs_889_: *mut LeanObject,
    mut v_k_890_: *mut LeanObject,
    mut v_inst_891_: *mut LeanObject,
    mut v___y_892_: *mut LeanObject,
    mut v___y_893_: *mut LeanObject,
    mut v___y_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    v___x_897_ = lean_unsigned_to_nat(1);
    v___x_898_ = lean_nat_add(v_i_887_, v___x_897_);
    v___x_899_ = lean_array_push(v_insts_888_, v_inst_891_);
    v___x_900_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_889_, v_k_890_, v___x_898_, v___x_899_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
    return v___x_900_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(
    mut v_xs_901_: *mut LeanObject,
    mut v_k_902_: *mut LeanObject,
    mut v_i_903_: *mut LeanObject,
    mut v_insts_904_: *mut LeanObject,
    mut v_a_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_910_: *mut LeanObject = core::ptr::null_mut();
    v_res_910_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_901_, v_k_902_, v_i_903_, v_insts_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
    lean_dec(v_a_908_);
    lean_dec_ref(v_a_907_);
    lean_dec(v_a_906_);
    lean_dec_ref(v_a_905_);
    return v_res_910_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(
    mut v_00_u03b1_911_: *mut LeanObject,
    mut v_xs_912_: *mut LeanObject,
    mut v_k_913_: *mut LeanObject,
    mut v_i_914_: *mut LeanObject,
    mut v_insts_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
    mut v_a_918_: *mut LeanObject,
    mut v_a_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    v___x_921_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_912_, v_k_913_, v_i_914_, v_insts_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
    return v___x_921_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(
    mut v_00_u03b1_922_: *mut LeanObject,
    mut v_xs_923_: *mut LeanObject,
    mut v_k_924_: *mut LeanObject,
    mut v_i_925_: *mut LeanObject,
    mut v_insts_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
    mut v_a_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_932_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_930_);
    lean_dec_ref(v_a_929_);
    lean_dec(v_a_928_);
    lean_dec_ref(v_a_927_);
    return v_res_932_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(
    mut v_xs_935_: *mut LeanObject,
    mut v_k_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
    mut v_a_938_: *mut LeanObject,
    mut v_a_939_: *mut LeanObject,
    mut v_a_940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___x_942_ = lean_unsigned_to_nat(0);
    v___x_943_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0;
    v___x_944_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_935_, v_k_936_, v___x_942_, v___x_943_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
    return v___x_944_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(
    mut v_xs_945_: *mut LeanObject,
    mut v_k_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
    mut v_a_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_952_: *mut LeanObject = core::ptr::null_mut();
    v_res_952_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_945_, v_k_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
    lean_dec(v_a_950_);
    lean_dec_ref(v_a_949_);
    lean_dec(v_a_948_);
    lean_dec_ref(v_a_947_);
    return v_res_952_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(
    mut v_00_u03b1_953_: *mut LeanObject,
    mut v_xs_954_: *mut LeanObject,
    mut v_k_955_: *mut LeanObject,
    mut v_a_956_: *mut LeanObject,
    mut v_a_957_: *mut LeanObject,
    mut v_a_958_: *mut LeanObject,
    mut v_a_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    v___x_961_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_954_, v_k_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
    return v___x_961_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(
    mut v_00_u03b1_962_: *mut LeanObject,
    mut v_xs_963_: *mut LeanObject,
    mut v_k_964_: *mut LeanObject,
    mut v_a_965_: *mut LeanObject,
    mut v_a_966_: *mut LeanObject,
    mut v_a_967_: *mut LeanObject,
    mut v_a_968_: *mut LeanObject,
    mut v_a_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_970_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_968_);
    lean_dec_ref(v_a_967_);
    lean_dec(v_a_966_);
    lean_dec_ref(v_a_965_);
    return v_res_970_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
    mut v_type_971_: *mut LeanObject,
    mut v_useOfNonempty_972_: u8,
    mut v_a_973_: *mut LeanObject,
    mut v_a_974_: *mut LeanObject,
    mut v_a_975_: *mut LeanObject,
    mut v_a_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_980_: u8 = 0;
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_992_: u8 = 0;
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_997_: u8 = 0;
    let mut v_a_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useOfNonempty_972_ == 0 {
                    v___x_988_ =
                        l_Lean_Meta_mkDefault(v_type_971_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
                    if lean_obj_tag(v___x_988_) == 0 {
                        v_a_989_ = lean_ctor_get(v___x_988_, 0);
                        v_isSharedCheck_997_ = (!lean_is_exclusive(v___x_988_)) as u8;
                        if v_isSharedCheck_997_ == 0 {
                            v___x_991_ = v___x_988_;
                            v_isShared_992_ = v_isSharedCheck_997_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_989_);
                            lean_dec(v___x_988_);
                            v___x_991_ = lean_box(0);
                            v_isShared_992_ = v_isSharedCheck_997_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_998_ = lean_ctor_get(v___x_988_, 0);
                        lean_inc(v_a_998_);
                        lean_dec_ref_known(v___x_988_, 1);
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
                    if lean_obj_tag(v___x_999_) == 0 {
                        v_a_1000_ = lean_ctor_get(v___x_999_, 0);
                        v_isSharedCheck_1008_ = (!lean_is_exclusive(v___x_999_)) as u8;
                        if v_isSharedCheck_1008_ == 0 {
                            v___x_1002_ = v___x_999_;
                            v_isShared_1003_ = v_isSharedCheck_1008_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1000_);
                            lean_dec(v___x_999_);
                            v___x_1002_ = lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1008_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1009_ = lean_ctor_get(v___x_999_, 0);
                        lean_inc(v_a_1009_);
                        lean_dec_ref_known(v___x_999_, 1);
                        v_a_985_ = v_a_1009_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_980_ == 0 {
                    lean_dec_ref(v___y_979_);
                    v___x_981_ = lean_box(0);
                    v___x_982_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_982_, 0, v___x_981_);
                    return v___x_982_;
                } else {
                    v___x_983_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_983_, 0, v___y_979_);
                    return v___x_983_;
                }
            }
            2 => {
                v___x_986_ = l_Lean_Exception_isInterrupt(v_a_985_);
                if v___x_986_ == 0 {
                    lean_inc_ref(v_a_985_);
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
                v___x_993_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_993_, 0, v_a_989_);
                if v_isShared_992_ == 0 {
                    lean_ctor_set(v___x_991_, 0, v___x_993_);
                    v___x_995_ = v___x_991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
                    v___x_995_ = v_reuseFailAlloc_996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_995_;
            }
            5 => {
                v___x_1004_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1004_, 0, v_a_1000_);
                if v_isShared_1003_ == 0 {
                    lean_ctor_set(v___x_1002_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
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
    mut v_type_1010_: *mut LeanObject,
    mut v_useOfNonempty_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
    mut v_a_1014_: *mut LeanObject,
    mut v_a_1015_: *mut LeanObject,
    mut v_a_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useOfNonempty_boxed_1017_: u8 = 0;
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1017_ = (lean_unbox(v_useOfNonempty_1011_) as u8);
    v_res_1018_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
        v_type_1010_,
        v_useOfNonempty_boxed_1017_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
    );
    lean_dec(v_a_1015_);
    lean_dec_ref(v_a_1014_);
    lean_dec(v_a_1013_);
    lean_dec_ref(v_a_1012_);
    return v_res_1018_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(
    mut v_k_1019_: *mut LeanObject,
    mut v_b_1020_: *mut LeanObject,
    mut v_c_1021_: *mut LeanObject,
    mut v___y_1022_: *mut LeanObject,
    mut v___y_1023_: *mut LeanObject,
    mut v___y_1024_: *mut LeanObject,
    mut v___y_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1025_);
    lean_inc_ref(v___y_1024_);
    lean_inc(v___y_1023_);
    lean_inc_ref(v___y_1022_);
    v___x_1027_ = lean_apply_7(
        v_k_1019_,
        v_b_1020_,
        v_c_1021_,
        v___y_1022_,
        v___y_1023_,
        v___y_1024_,
        v___y_1025_,
        lean_box(0),
    );
    return v___x_1027_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(
    mut v_k_1028_: *mut LeanObject,
    mut v_b_1029_: *mut LeanObject,
    mut v_c_1030_: *mut LeanObject,
    mut v___y_1031_: *mut LeanObject,
    mut v___y_1032_: *mut LeanObject,
    mut v___y_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_1028_, v_b_1029_, v_c_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
    lean_dec(v___y_1034_);
    lean_dec_ref(v___y_1033_);
    lean_dec(v___y_1032_);
    lean_dec_ref(v___y_1031_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(
    mut v_type_1037_: *mut LeanObject,
    mut v_k_1038_: *mut LeanObject,
    mut v_cleanupAnnotations_1039_: u8,
    mut v___y_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
    mut v___y_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1045_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1045_, 0, v_k_1038_);
                v___x_1046_ = 0;
                v___x_1047_ = lean_box(0);
                v___x_1048_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
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
                if lean_obj_tag(v___x_1048_) == 0 {
                    v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1056_ = (!lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1051_ = v___x_1048_;
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1049_);
                        lean_dec(v___x_1048_);
                        v___x_1051_ = lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1057_ = lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1064_ = (!lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1064_ == 0 {
                        v___x_1059_ = v___x_1048_;
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1057_);
                        lean_dec(v___x_1048_);
                        v___x_1059_ = lean_box(0);
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
                    v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
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
                    v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
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
    mut v_type_1065_: *mut LeanObject,
    mut v_k_1066_: *mut LeanObject,
    mut v_cleanupAnnotations_1067_: *mut LeanObject,
    mut v___y_1068_: *mut LeanObject,
    mut v___y_1069_: *mut LeanObject,
    mut v___y_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1073_: u8 = 0;
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1073_ = (lean_unbox(v_cleanupAnnotations_1067_) as u8);
    v_res_1074_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_1065_, v_k_1066_, v_cleanupAnnotations_boxed_1073_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
    lean_dec(v___y_1071_);
    lean_dec_ref(v___y_1070_);
    lean_dec(v___y_1069_);
    lean_dec_ref(v___y_1068_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(
    mut v_00_u03b1_1075_: *mut LeanObject,
    mut v_type_1076_: *mut LeanObject,
    mut v_k_1077_: *mut LeanObject,
    mut v_cleanupAnnotations_1078_: u8,
    mut v___y_1079_: *mut LeanObject,
    mut v___y_1080_: *mut LeanObject,
    mut v___y_1081_: *mut LeanObject,
    mut v___y_1082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_1076_, v_k_1077_, v_cleanupAnnotations_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
    return v___x_1084_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(
    mut v_00_u03b1_1085_: *mut LeanObject,
    mut v_type_1086_: *mut LeanObject,
    mut v_k_1087_: *mut LeanObject,
    mut v_cleanupAnnotations_1088_: *mut LeanObject,
    mut v___y_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1094_: u8 = 0;
    let mut v_res_1095_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1094_ = (lean_unbox(v_cleanupAnnotations_1088_) as u8);
    v_res_1095_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(v_00_u03b1_1085_, v_type_1086_, v_k_1087_, v_cleanupAnnotations_boxed_1094_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
    lean_dec(v___y_1092_);
    lean_dec_ref(v___y_1091_);
    lean_dec(v___y_1090_);
    lean_dec_ref(v___y_1089_);
    return v_res_1095_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1102_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1102_, 0, v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3);
    v___x_1104_ = l_Lean_MessageData_ofFormat(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v___x_1105_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4);
    v___x_1106_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2;
    v___x_1107_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    lean_ctor_set(v___x_1107_, 1, v___x_1105_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(
    mut v_ref_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    v___x_1110_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5);
    v___x_1111_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1111_, 0, v_ref_1108_);
    lean_ctor_set(v___x_1111_, 1, v___x_1110_);
    v___x_1112_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1112_, 0, v___x_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(
    mut v_ref_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1115_: *mut LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1113_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(
    mut v_00_u03b1_1116_: *mut LeanObject,
    mut v_ref_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1117_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(
    mut v_00_u03b1_1124_: *mut LeanObject,
    mut v_ref_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(v_00_u03b1_1124_, v_ref_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
    lean_dec(v___y_1129_);
    lean_dec_ref(v___y_1128_);
    lean_dec(v___y_1127_);
    lean_dec_ref(v___y_1126_);
    return v_res_1131_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(
    mut v_xs_1132_: *mut LeanObject,
    mut v_insts_1133_: *mut LeanObject,
    mut v_useOfNonempty_1134_: *mut LeanObject,
    mut v_xs_x27_1135_: *mut LeanObject,
    mut v_type_x27_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useOfNonempty_boxed_1142_: u8 = 0;
    let mut v_res_1143_: *mut LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1142_ = (lean_unbox(v_useOfNonempty_1134_) as u8);
    v_res_1143_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_1132_, v_insts_1133_, v_useOfNonempty_boxed_1142_, v_xs_x27_1135_, v_type_x27_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
    lean_dec(v___y_1140_);
    lean_dec_ref(v___y_1139_);
    lean_dec(v___y_1138_);
    lean_dec_ref(v___y_1137_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(
    mut v_xs_1144_: *mut LeanObject,
    mut v_insts_1145_: *mut LeanObject,
    mut v_type_1146_: *mut LeanObject,
    mut v_useOfNonempty_1147_: u8,
    mut v_a_1148_: *mut LeanObject,
    mut v_a_1149_: *mut LeanObject,
    mut v_a_1150_: *mut LeanObject,
    mut v_a_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1165_: u8 = 0;
    let mut v_cancelTk_x3f_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1167_: u8 = 0;
    let mut v_inheritedTraceOptions_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut v_a_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_a_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v_val_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: u8 = 0;
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1153_ = lean_ctor_get(v_a_1150_, 0);
                lean_inc_ref(v_fileName_1153_);
                v_fileMap_1154_ = lean_ctor_get(v_a_1150_, 1);
                lean_inc_ref(v_fileMap_1154_);
                v_options_1155_ = lean_ctor_get(v_a_1150_, 2);
                lean_inc_ref(v_options_1155_);
                v_currRecDepth_1156_ = lean_ctor_get(v_a_1150_, 3);
                lean_inc(v_currRecDepth_1156_);
                v_maxRecDepth_1157_ = lean_ctor_get(v_a_1150_, 4);
                lean_inc(v_maxRecDepth_1157_);
                v_ref_1158_ = lean_ctor_get(v_a_1150_, 5);
                lean_inc(v_ref_1158_);
                v_currNamespace_1159_ = lean_ctor_get(v_a_1150_, 6);
                lean_inc(v_currNamespace_1159_);
                v_openDecls_1160_ = lean_ctor_get(v_a_1150_, 7);
                lean_inc(v_openDecls_1160_);
                v_initHeartbeats_1161_ = lean_ctor_get(v_a_1150_, 8);
                lean_inc(v_initHeartbeats_1161_);
                v_maxHeartbeats_1162_ = lean_ctor_get(v_a_1150_, 9);
                lean_inc(v_maxHeartbeats_1162_);
                v_quotContext_1163_ = lean_ctor_get(v_a_1150_, 10);
                lean_inc(v_quotContext_1163_);
                v_currMacroScope_1164_ = lean_ctor_get(v_a_1150_, 11);
                lean_inc(v_currMacroScope_1164_);
                v_diag_1165_ = lean_ctor_get_uint8(
                    v_a_1150_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1166_ = lean_ctor_get(v_a_1150_, 12);
                lean_inc(v_cancelTk_x3f_1166_);
                v_suppressElabErrors_1167_ = lean_ctor_get_uint8(
                    v_a_1150_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1168_ = lean_ctor_get(v_a_1150_, 13);
                lean_inc_ref(v_inheritedTraceOptions_1168_);
                lean_dec_ref(v_a_1150_);
                v___x_1169_ = lean_box((v_useOfNonempty_1147_) as usize);
                lean_inc_ref(v_insts_1145_);
                lean_inc_ref(v_xs_1144_);
                v___f_1170_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_1170_, 0, v_xs_1144_);
                lean_closure_set(v___f_1170_, 1, v_insts_1145_);
                lean_closure_set(v___f_1170_, 2, v___x_1169_);
                v___x_1240_ = lean_unsigned_to_nat(0);
                v___x_1241_ = lean_nat_dec_eq(v_maxRecDepth_1157_, v___x_1240_);
                if v___x_1241_ == 0 {
                    v___x_1242_ = lean_nat_dec_eq(v_currRecDepth_1156_, v_maxRecDepth_1157_);
                    if v___x_1242_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___f_1170_);
                        lean_dec_ref(v_inheritedTraceOptions_1168_);
                        lean_dec(v_cancelTk_x3f_1166_);
                        lean_dec(v_currMacroScope_1164_);
                        lean_dec(v_quotContext_1163_);
                        lean_dec(v_maxHeartbeats_1162_);
                        lean_dec(v_initHeartbeats_1161_);
                        lean_dec(v_openDecls_1160_);
                        lean_dec(v_currNamespace_1159_);
                        lean_dec(v_maxRecDepth_1157_);
                        lean_dec(v_currRecDepth_1156_);
                        lean_dec_ref(v_options_1155_);
                        lean_dec_ref(v_fileMap_1154_);
                        lean_dec_ref(v_fileName_1153_);
                        lean_dec_ref(v_type_1146_);
                        lean_dec_ref(v_insts_1145_);
                        lean_dec_ref(v_xs_1144_);
                        v___x_1243_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_1158_);
                        return v___x_1243_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1172_ = lean_unsigned_to_nat(1);
                v___x_1173_ = lean_nat_add(v_currRecDepth_1156_, v___x_1172_);
                lean_dec(v_currRecDepth_1156_);
                v___x_1174_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1174_, 0, v_fileName_1153_);
                lean_ctor_set(v___x_1174_, 1, v_fileMap_1154_);
                lean_ctor_set(v___x_1174_, 2, v_options_1155_);
                lean_ctor_set(v___x_1174_, 3, v___x_1173_);
                lean_ctor_set(v___x_1174_, 4, v_maxRecDepth_1157_);
                lean_ctor_set(v___x_1174_, 5, v_ref_1158_);
                lean_ctor_set(v___x_1174_, 6, v_currNamespace_1159_);
                lean_ctor_set(v___x_1174_, 7, v_openDecls_1160_);
                lean_ctor_set(v___x_1174_, 8, v_initHeartbeats_1161_);
                lean_ctor_set(v___x_1174_, 9, v_maxHeartbeats_1162_);
                lean_ctor_set(v___x_1174_, 10, v_quotContext_1163_);
                lean_ctor_set(v___x_1174_, 11, v_currMacroScope_1164_);
                lean_ctor_set(v___x_1174_, 12, v_cancelTk_x3f_1166_);
                lean_ctor_set(v___x_1174_, 13, v_inheritedTraceOptions_1168_);
                lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_1165_,
                );
                lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1167_,
                );
                lean_inc_ref(v_type_1146_);
                v___x_1175_ =
                    l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(
                        v_type_1146_,
                        v_useOfNonempty_1147_,
                        v_a_1148_,
                        v_a_1149_,
                        v___x_1174_,
                        v_a_1151_,
                    );
                if lean_obj_tag(v___x_1175_) == 0 {
                    v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
                    lean_inc(v_a_1176_);
                    lean_dec_ref_known(v___x_1175_, 1);
                    if lean_obj_tag(v_a_1176_) == 1 {
                        lean_dec_ref(v___f_1170_);
                        lean_dec_ref(v_type_1146_);
                        v_val_1177_ = lean_ctor_get(v_a_1176_, 0);
                        v_isSharedCheck_1214_ = (!lean_is_exclusive(v_a_1176_)) as u8;
                        if v_isSharedCheck_1214_ == 0 {
                            v___x_1179_ = v_a_1176_;
                            v_isShared_1180_ = v_isSharedCheck_1214_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_1177_);
                            lean_dec(v_a_1176_);
                            v___x_1179_ = lean_box(0);
                            v_isShared_1180_ = v_isSharedCheck_1214_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1176_);
                        v___x_1215_ = l_Lean_Meta_whnfCore(
                            v_type_1146_,
                            v_a_1148_,
                            v_a_1149_,
                            v___x_1174_,
                            v_a_1151_,
                        );
                        if lean_obj_tag(v___x_1215_) == 0 {
                            v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
                            lean_inc(v_a_1216_);
                            lean_dec_ref_known(v___x_1215_, 1);
                            v___x_1217_ = l_Lean_Expr_isForall(v_a_1216_);
                            if v___x_1217_ == 0 {
                                lean_dec_ref(v___f_1170_);
                                v___x_1218_ = l_Lean_Meta_unfoldDefinition_x3f(
                                    v_a_1216_,
                                    v___x_1217_,
                                    v_a_1148_,
                                    v_a_1149_,
                                    v___x_1174_,
                                    v_a_1151_,
                                );
                                if lean_obj_tag(v___x_1218_) == 0 {
                                    v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
                                    v_isSharedCheck_1229_ = (!lean_is_exclusive(v___x_1218_)) as u8;
                                    if v_isSharedCheck_1229_ == 0 {
                                        v___x_1221_ = v___x_1218_;
                                        v_isShared_1222_ = v_isSharedCheck_1229_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1219_);
                                        lean_dec(v___x_1218_);
                                        v___x_1221_ = lean_box(0);
                                        v_isShared_1222_ = v_isSharedCheck_1229_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_1174_, 14);
                                    lean_dec_ref(v_insts_1145_);
                                    lean_dec_ref(v_xs_1144_);
                                    return v___x_1218_;
                                }
                            } else {
                                lean_dec_ref(v_insts_1145_);
                                lean_dec_ref(v_xs_1144_);
                                v___x_1230_ = 0;
                                v___x_1231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_a_1216_, v___f_1170_, v___x_1230_, v_a_1148_, v_a_1149_, v___x_1174_, v_a_1151_);
                                lean_dec_ref_known(v___x_1174_, 14);
                                return v___x_1231_;
                            }
                        } else {
                            lean_dec_ref_known(v___x_1174_, 14);
                            lean_dec_ref(v___f_1170_);
                            lean_dec_ref(v_insts_1145_);
                            lean_dec_ref(v_xs_1144_);
                            v_a_1232_ = lean_ctor_get(v___x_1215_, 0);
                            v_isSharedCheck_1239_ = (!lean_is_exclusive(v___x_1215_)) as u8;
                            if v_isSharedCheck_1239_ == 0 {
                                v___x_1234_ = v___x_1215_;
                                v_isShared_1235_ = v_isSharedCheck_1239_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_1232_);
                                lean_dec(v___x_1215_);
                                v___x_1234_ = lean_box(0);
                                v_isShared_1235_ = v_isSharedCheck_1239_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_1174_, 14);
                    lean_dec_ref(v___f_1170_);
                    lean_dec_ref(v_type_1146_);
                    lean_dec_ref(v_insts_1145_);
                    lean_dec_ref(v_xs_1144_);
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
                lean_dec_ref(v_insts_1145_);
                if lean_obj_tag(v___x_1183_) == 0 {
                    v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
                    lean_inc(v_a_1184_);
                    lean_dec_ref_known(v___x_1183_, 1);
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
                    lean_dec_ref_known(v___x_1174_, 14);
                    lean_dec_ref(v_xs_1144_);
                    if lean_obj_tag(v___x_1186_) == 0 {
                        v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
                        v_isSharedCheck_1197_ = (!lean_is_exclusive(v___x_1186_)) as u8;
                        if v_isSharedCheck_1197_ == 0 {
                            v___x_1189_ = v___x_1186_;
                            v_isShared_1190_ = v_isSharedCheck_1197_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1187_);
                            lean_dec(v___x_1186_);
                            v___x_1189_ = lean_box(0);
                            v_isShared_1190_ = v_isSharedCheck_1197_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1179_);
                        v_a_1198_ = lean_ctor_get(v___x_1186_, 0);
                        v_isSharedCheck_1205_ = (!lean_is_exclusive(v___x_1186_)) as u8;
                        if v_isSharedCheck_1205_ == 0 {
                            v___x_1200_ = v___x_1186_;
                            v_isShared_1201_ = v_isSharedCheck_1205_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1198_);
                            lean_dec(v___x_1186_);
                            v___x_1200_ = lean_box(0);
                            v_isShared_1201_ = v_isSharedCheck_1205_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1179_);
                    lean_dec_ref_known(v___x_1174_, 14);
                    lean_dec_ref(v_xs_1144_);
                    v_a_1206_ = lean_ctor_get(v___x_1183_, 0);
                    v_isSharedCheck_1213_ = (!lean_is_exclusive(v___x_1183_)) as u8;
                    if v_isSharedCheck_1213_ == 0 {
                        v___x_1208_ = v___x_1183_;
                        v_isShared_1209_ = v_isSharedCheck_1213_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1206_);
                        lean_dec(v___x_1183_);
                        v___x_1208_ = lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1213_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1180_ == 0 {
                    lean_ctor_set(v___x_1179_, 0, v_a_1187_);
                    v___x_1192_ = v___x_1179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1187_);
                    v___x_1192_ = v_reuseFailAlloc_1196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1190_ == 0 {
                    lean_ctor_set(v___x_1189_, 0, v___x_1192_);
                    v___x_1194_ = v___x_1189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
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
                    v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
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
                    v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1211_;
            }
            10 => {
                if lean_obj_tag(v_a_1219_) == 1 {
                    lean_del_object(v___x_1221_);
                    v_val_1223_ = lean_ctor_get(v_a_1219_, 0);
                    lean_inc(v_val_1223_);
                    lean_dec_ref_known(v_a_1219_, 1);
                    v_type_1146_ = v_val_1223_;
                    v_a_1150_ = v___x_1174_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_1219_);
                    lean_dec_ref_known(v___x_1174_, 14);
                    lean_dec_ref(v_insts_1145_);
                    lean_dec_ref(v_xs_1144_);
                    v___x_1225_ = lean_box(0);
                    if v_isShared_1222_ == 0 {
                        lean_ctor_set(v___x_1221_, 0, v___x_1225_);
                        v___x_1227_ = v___x_1221_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
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
                    v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
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
    mut v_xs_1244_: *mut LeanObject,
    mut v_xs_x27_1245_: *mut LeanObject,
    mut v_insts_1246_: *mut LeanObject,
    mut v_type_x27_1247_: *mut LeanObject,
    mut v_useOfNonempty_1248_: u8,
    mut v_insts_x27_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Array_append___redArg(v_xs_1244_, v_xs_x27_1245_);
    v___x_1256_ = l_Array_append___redArg(v_insts_1246_, v_insts_x27_1249_);
    lean_inc_ref(v___y_1252_);
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
    mut v_xs_1258_: *mut LeanObject,
    mut v_xs_x27_1259_: *mut LeanObject,
    mut v_insts_1260_: *mut LeanObject,
    mut v_type_x27_1261_: *mut LeanObject,
    mut v_useOfNonempty_1262_: *mut LeanObject,
    mut v_insts_x27_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useOfNonempty_boxed_1269_: u8 = 0;
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1269_ = (lean_unbox(v_useOfNonempty_1262_) as u8);
    v_res_1270_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_1258_, v_xs_x27_1259_, v_insts_1260_, v_type_x27_1261_, v_useOfNonempty_boxed_1269_, v_insts_x27_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    lean_dec(v___y_1267_);
    lean_dec_ref(v___y_1266_);
    lean_dec(v___y_1265_);
    lean_dec_ref(v___y_1264_);
    lean_dec_ref(v_insts_x27_1263_);
    lean_dec_ref(v_xs_x27_1259_);
    return v_res_1270_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(
    mut v_xs_1271_: *mut LeanObject,
    mut v_insts_1272_: *mut LeanObject,
    mut v_useOfNonempty_1273_: u8,
    mut v_xs_x27_1274_: *mut LeanObject,
    mut v_type_x27_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = lean_box((v_useOfNonempty_1273_) as usize);
    lean_inc_ref(v_xs_x27_1274_);
    v___f_1282_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
    lean_closure_set(v___f_1282_, 0, v_xs_1271_);
    lean_closure_set(v___f_1282_, 1, v_xs_x27_1274_);
    lean_closure_set(v___f_1282_, 2, v_insts_1272_);
    lean_closure_set(v___f_1282_, 3, v_type_x27_1275_);
    lean_closure_set(v___f_1282_, 4, v___x_1281_);
    v___x_1283_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_x27_1274_, v___f_1282_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
    return v___x_1283_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(
    mut v_xs_1284_: *mut LeanObject,
    mut v_insts_1285_: *mut LeanObject,
    mut v_type_1286_: *mut LeanObject,
    mut v_useOfNonempty_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useOfNonempty_boxed_1293_: u8 = 0;
    let mut v_res_1294_: *mut LeanObject = core::ptr::null_mut();
    v_useOfNonempty_boxed_1293_ = (lean_unbox(v_useOfNonempty_1287_) as u8);
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
    lean_dec(v_a_1291_);
    lean_dec(v_a_1289_);
    lean_dec_ref(v_a_1288_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(
    mut v_msgData_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    v___x_1301_ = lean_st_ref_get(v___y_1299_);
    v_env_1302_ = lean_ctor_get(v___x_1301_, 0);
    lean_inc_ref(v_env_1302_);
    lean_dec(v___x_1301_);
    v___x_1303_ = lean_st_ref_get(v___y_1297_);
    v_mctx_1304_ = lean_ctor_get(v___x_1303_, 0);
    lean_inc_ref(v_mctx_1304_);
    lean_dec(v___x_1303_);
    v_lctx_1305_ = lean_ctor_get(v___y_1296_, 2);
    v_options_1306_ = lean_ctor_get(v___y_1298_, 2);
    lean_inc_ref(v_options_1306_);
    lean_inc_ref(v_lctx_1305_);
    v___x_1307_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1307_, 0, v_env_1302_);
    lean_ctor_set(v___x_1307_, 1, v_mctx_1304_);
    lean_ctor_set(v___x_1307_, 2, v_lctx_1305_);
    lean_ctor_set(v___x_1307_, 3, v_options_1306_);
    v___x_1308_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1308_, 0, v___x_1307_);
    lean_ctor_set(v___x_1308_, 1, v_msgData_1295_);
    v___x_1309_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1309_, 0, v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(
    mut v_msgData_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1316_: *mut LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
    lean_dec(v___y_1314_);
    lean_dec_ref(v___y_1313_);
    lean_dec(v___y_1312_);
    lean_dec_ref(v___y_1311_);
    return v_res_1316_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
    mut v_msg_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1323_ = lean_ctor_get(v___y_1320_, 5);
                v___x_1324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
                v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
                v_isSharedCheck_1333_ = (!lean_is_exclusive(v___x_1324_)) as u8;
                if v_isSharedCheck_1333_ == 0 {
                    v___x_1327_ = v___x_1324_;
                    v_isShared_1328_ = v_isSharedCheck_1333_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1325_);
                    lean_dec(v___x_1324_);
                    v___x_1327_ = lean_box(0);
                    v_isShared_1328_ = v_isSharedCheck_1333_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1323_);
                v___x_1329_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1329_, 0, v_ref_1323_);
                lean_ctor_set(v___x_1329_, 1, v_a_1325_);
                if v_isShared_1328_ == 0 {
                    lean_ctor_set_tag(v___x_1327_, 1);
                    lean_ctor_set(v___x_1327_, 0, v___x_1329_);
                    v___x_1331_ = v___x_1327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
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
    mut v_msg_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
    mut v___y_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(
        v_msg_1334_,
        v___y_1335_,
        v___y_1336_,
        v___y_1337_,
        v___y_1338_,
    );
    lean_dec(v___y_1338_);
    lean_dec_ref(v___y_1337_);
    lean_dec(v___y_1336_);
    lean_dec_ref(v___y_1335_);
    return v_res_1340_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__0;
    v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__2;
    v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = 0;
    v___x_1348_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1;
    v___x_1349_ = l_Lean_MessageData_ofConstName(v___x_1348_, v___x_1347_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__5;
    v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9() -> *mut LeanObject {
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = 0;
    v___x_1357_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__8;
    v___x_1358_ = l_Lean_MessageData_ofConstName(v___x_1357_, v___x_1356_);
    return v___x_1358_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__10;
    v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13() -> *mut LeanObject {
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Elab_mkInhabitantFor___lam__0___closed__12;
    v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___lam__0(
    mut v_xs_1365_: *mut LeanObject,
    mut v_type_1366_: *mut LeanObject,
    mut v_failedToMessage_1367_: *mut LeanObject,
    mut v_insts_1368_: *mut LeanObject,
    mut v___y_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1374_: u8 = 0;
    let mut v___y_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v_val_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_a_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1374_ = 0;
                lean_inc_ref(v___y_1371_);
                lean_inc_ref(v_type_1366_);
                lean_inc_ref(v_insts_1368_);
                lean_inc_ref(v_xs_1365_);
                v___x_1416_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_1365_, v_insts_1368_, v_type_1366_, v___x_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                if lean_obj_tag(v___x_1416_) == 0 {
                    v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
                    lean_inc(v_a_1417_);
                    if lean_obj_tag(v_a_1417_) == 0 {
                        lean_dec_ref_known(v___x_1416_, 1);
                        v___x_1418_ = 1;
                        lean_inc_ref(v___y_1371_);
                        lean_inc_ref(v_type_1366_);
                        lean_inc_ref(v_xs_1365_);
                        v___x_1419_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_1365_, v_insts_1368_, v_type_1366_, v___x_1418_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                        v___y_1376_ = v___x_1419_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_1417_, 1);
                        lean_dec_ref(v_insts_1368_);
                        v___y_1376_ = v___x_1416_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_insts_1368_);
                    v___y_1376_ = v___x_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_1376_) == 0 {
                    v_a_1377_ = lean_ctor_get(v___y_1376_, 0);
                    v_isSharedCheck_1407_ = (!lean_is_exclusive(v___y_1376_)) as u8;
                    if v_isSharedCheck_1407_ == 0 {
                        v___x_1379_ = v___y_1376_;
                        v_isShared_1380_ = v_isSharedCheck_1407_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1377_);
                        lean_dec(v___y_1376_);
                        v___x_1379_ = lean_box(0);
                        v_isShared_1380_ = v_isSharedCheck_1407_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_failedToMessage_1367_);
                    lean_dec_ref(v_type_1366_);
                    lean_dec_ref(v_xs_1365_);
                    v_a_1408_ = lean_ctor_get(v___y_1376_, 0);
                    v_isSharedCheck_1415_ = (!lean_is_exclusive(v___y_1376_)) as u8;
                    if v_isSharedCheck_1415_ == 0 {
                        v___x_1410_ = v___y_1376_;
                        v_isShared_1411_ = v_isSharedCheck_1415_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1408_);
                        lean_dec(v___y_1376_);
                        v___x_1410_ = lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1415_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1377_) == 1 {
                    lean_dec_ref(v_failedToMessage_1367_);
                    lean_dec_ref(v_type_1366_);
                    lean_dec_ref(v_xs_1365_);
                    v_val_1381_ = lean_ctor_get(v_a_1377_, 0);
                    lean_inc(v_val_1381_);
                    lean_dec_ref_known(v_a_1377_, 1);
                    if v_isShared_1380_ == 0 {
                        lean_ctor_set(v___x_1379_, 0, v_val_1381_);
                        v___x_1383_ = v___x_1379_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_val_1381_);
                        v___x_1383_ = v_reuseFailAlloc_1384_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1379_);
                    lean_dec(v_a_1377_);
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
                    lean_dec_ref(v_xs_1365_);
                    if lean_obj_tag(v___x_1387_) == 0 {
                        v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
                        lean_inc(v_a_1388_);
                        lean_dec_ref_known(v___x_1387_, 1);
                        v___x_1389_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1,
                        );
                        v___x_1390_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1390_, 0, v_failedToMessage_1367_);
                        lean_ctor_set(v___x_1390_, 1, v___x_1389_);
                        v___x_1391_ = l_Lean_indentExpr(v_a_1388_);
                        v___x_1392_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1392_, 0, v___x_1390_);
                        lean_ctor_set(v___x_1392_, 1, v___x_1391_);
                        v___x_1393_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3,
                        );
                        v___x_1394_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1394_, 0, v___x_1392_);
                        lean_ctor_set(v___x_1394_, 1, v___x_1393_);
                        v___x_1395_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4,
                        );
                        v___x_1396_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1396_, 0, v___x_1394_);
                        lean_ctor_set(v___x_1396_, 1, v___x_1395_);
                        v___x_1397_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6,
                        );
                        v___x_1398_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1398_, 0, v___x_1396_);
                        lean_ctor_set(v___x_1398_, 1, v___x_1397_);
                        v___x_1399_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9,
                        );
                        v___x_1400_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1400_, 0, v___x_1398_);
                        lean_ctor_set(v___x_1400_, 1, v___x_1399_);
                        v___x_1401_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11,
                        );
                        v___x_1402_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1402_, 0, v___x_1400_);
                        lean_ctor_set(v___x_1402_, 1, v___x_1401_);
                        v___x_1403_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1403_, 0, v___x_1402_);
                        lean_ctor_set(v___x_1403_, 1, v___x_1395_);
                        v___x_1404_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once
                            ),
                            _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13,
                        );
                        v___x_1405_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1405_, 0, v___x_1403_);
                        lean_ctor_set(v___x_1405_, 1, v___x_1404_);
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
                        lean_dec_ref(v_failedToMessage_1367_);
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
                    v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
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
    mut v_xs_1420_: *mut LeanObject,
    mut v_type_1421_: *mut LeanObject,
    mut v_failedToMessage_1422_: *mut LeanObject,
    mut v_insts_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
    mut v___y_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1427_);
    lean_dec_ref(v___y_1426_);
    lean_dec(v___y_1425_);
    lean_dec_ref(v___y_1424_);
    return v_res_1429_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor(
    mut v_failedToMessage_1430_: *mut LeanObject,
    mut v_xs_1431_: *mut LeanObject,
    mut v_type_1432_: *mut LeanObject,
    mut v_a_1433_: *mut LeanObject,
    mut v_a_1434_: *mut LeanObject,
    mut v_a_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_xs_1431_);
    v___f_1438_ = lean_alloc_closure(
        l_Lean_Elab_mkInhabitantFor___lam__0___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_1438_, 0, v_xs_1431_);
    lean_closure_set(v___f_1438_, 1, v_type_1432_);
    lean_closure_set(v___f_1438_, 2, v_failedToMessage_1430_);
    v___x_1439_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_1431_, v___f_1438_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Elab_mkInhabitantFor___boxed(
    mut v_failedToMessage_1440_: *mut LeanObject,
    mut v_xs_1441_: *mut LeanObject,
    mut v_type_1442_: *mut LeanObject,
    mut v_a_1443_: *mut LeanObject,
    mut v_a_1444_: *mut LeanObject,
    mut v_a_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_a_1447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1448_: *mut LeanObject = core::ptr::null_mut();
    v_res_1448_ = l_Lean_Elab_mkInhabitantFor(
        v_failedToMessage_1440_,
        v_xs_1441_,
        v_type_1442_,
        v_a_1443_,
        v_a_1444_,
        v_a_1445_,
        v_a_1446_,
    );
    lean_dec(v_a_1446_);
    lean_dec_ref(v_a_1445_);
    lean_dec(v_a_1444_);
    lean_dec_ref(v_a_1443_);
    return v_res_1448_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(
    mut v_00_u03b1_1449_: *mut LeanObject,
    mut v_msg_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1457_: *mut LeanObject,
    mut v_msg_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1464_: *mut LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(
        v_00_u03b1_1457_,
        v_msg_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
    );
    lean_dec(v___y_1462_);
    lean_dec_ref(v___y_1461_);
    lean_dec(v___y_1460_);
    lean_dec_ref(v___y_1459_);
    return v_res_1464_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
}
