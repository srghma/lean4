// Lean compiler output
// Module: Lean.Data.Lsp.CodeActions
// Imports: Lean.Data.Lsp.Diagnostics
use crate::ffi::{
    lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_nat_dec_eq, lean_string_append, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD,
    l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromInt,
    l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    l_Lean_Lsp_instFromJsonCommand_fromJson, l_Lean_Lsp_instFromJsonResolveSupport_fromJson,
    l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson, l_Lean_Lsp_instToJsonCommand_toJson,
    l_Lean_Lsp_instToJsonResolveSupport_toJson, l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson,
    l_Lean_Lsp_instToJsonWorkspaceEdit_toJson,
};
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    l_Lean_Lsp_instFromJsonRange_fromJson, l_Lean_Lsp_instToJsonRange_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Diagnostics::{
    initialize_Lean_Data_Lsp_Diagnostics,
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson,
    l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson,
    runtime_initialize_Lean_Data_Lsp_Diagnostics,
};
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonCodeActionTriggerKind___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionTriggerKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 67, 111, 100, 101, 65, 99, 116, 105,
        111, 110, 84, 114, 105, 103, 103, 101, 114, 75, 105, 110, 100, 32, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionTriggerKind___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionTriggerKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionTriggerKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionTriggerKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionTriggerKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2_spec__4___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6_spec__8___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6_spec__8___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 84, 97, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__0_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 111, 114, 32, 105, 110, 116, 101, 103, 101, 114, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 99, 111, 100, 101, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15_spec__25___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15_spec__25___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15_spec__25___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 76, 101, 97, 110, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 84, 97, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__0_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 83, 101, 118, 101, 114, 105, 116, 121, 32, 39, 0]};
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 97, 110, 103, 101, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [76, 115, 112, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__3_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 87, 105, 116, 104, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject,2863902399367947479 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject,12743603005877258865 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__13_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 117, 108, 108, 82, 97, 110, 103, 101, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__14_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 117, 108, 108, 82, 97, 110, 103, 101, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__14_value) as *mut leanh::LeanObject,18167956084314672844 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__15_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__19_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 101, 118, 101, 114, 105, 116, 121, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__20_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 101, 118, 101, 114, 105, 116, 121, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__20_value) as *mut leanh::LeanObject,2339750138993587592 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__21_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__25_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 115, 83, 105, 108, 101, 110, 116, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__26_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 115, 83, 105, 108, 101, 110, 116, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__26_value) as *mut leanh::LeanObject,6916285088056307392 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__27_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__28_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__28: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__29_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__29: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__30: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__31_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__31_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__32_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 100, 101, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__32_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__32_value) as *mut leanh::LeanObject,3386430046879539552 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__33_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__35: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__37_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 111, 117, 114, 99, 101, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__37_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__38_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 111, 117, 114, 99, 101, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__38_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__38_value) as *mut leanh::LeanObject,7764395542335372806 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__39_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__40_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__40: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__41_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__41: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__42_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__42: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__43_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__43_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__43_value) as *mut leanh::LeanObject,982637797389909653 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__44_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__45_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__45: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__46_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__46: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__47_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__47: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__48_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 97, 103, 115, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__48_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__49_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 97, 103, 115, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__49_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__49_value) as *mut leanh::LeanObject,10757207218291958112 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__50_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__51_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__51: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__52_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__52: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__53_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__53: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__54_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 84, 97, 103, 115, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__54_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__55_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 97, 110, 84, 97, 103, 115, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__55_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__55_value) as *mut leanh::LeanObject,7655102125566572746 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__56_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__57_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__57: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__58_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__58: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__59_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__59: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__60_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [114, 101, 108, 97, 116, 101, 100, 73, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__60_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__61_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [114, 101, 108, 97, 116, 101, 100, 73, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 63, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__61_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__62_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__61_value) as *mut leanh::LeanObject,15798532268063128341 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__62_value) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__63_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__63: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__64_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__64: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__65_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__65: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 97, 116, 97, 0]};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__1_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 67, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        15725035349457982419 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        16258271359659748332 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__9_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [111, 110, 108, 121, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 110, 108, 121, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__10_value)
            as *mut leanh::LeanObject,
        5977700792363408356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__15_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 114, 105, 103, 103, 101, 114, 75, 105, 110, 100, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__16_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 114, 105, 103, 103, 101, 114, 75, 105, 110, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__16_value)
            as *mut leanh::LeanObject,
        3917655856709608029 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionContext___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionContext_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionContext___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionContext: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionContext___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionContext___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionContext_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionContext___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionContext: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        119, 111, 114, 107, 68, 111, 110, 101, 84, 111, 107, 101, 110, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__1_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        9963776826799994591 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__5_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        119, 111, 114, 107, 68, 111, 110, 101, 84, 111, 107, 101, 110, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__5_value)
            as *mut leanh::LeanObject,
        1758740783086273383 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        112, 97, 114, 116, 105, 97, 108, 82, 101, 115, 117, 108, 116, 84, 111, 107, 101, 110, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__11_value:
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
        112, 97, 114, 116, 105, 97, 108, 82, 101, 115, 117, 108, 116, 84, 111, 107, 101, 110, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__11_value)
            as *mut leanh::LeanObject,
        18406335021951492893 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__16_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__16_value)
            as *mut leanh::LeanObject,
        18338692295241883607 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__23_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 110, 116, 101, 120, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__24_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__23_value)
            as *mut leanh::LeanObject,
        8547351212575089967 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__24_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionParams___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionParams___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 101, 97, 115, 111, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__1_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 68, 105, 115, 97, 98, 108, 101, 100, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        9354359017271877727 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        3593801426820518423 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionDisabled___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionDisabled___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionDisabled: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionDisabled___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionDisabled___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionDisabled_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionDisabled___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionDisabled___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionDisabled: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionDisabled___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        119, 111, 114, 107, 68, 111, 110, 101, 80, 114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__1_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 75, 105, 110, 100, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__2_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        114, 101, 115, 111, 108, 118, 101, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionOptions___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionOptions_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 79, 112, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        18014963591880129808 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        642707601685617694 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__8_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 75, 105, 110, 100, 115, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__8_value)
            as *mut leanh::LeanObject,
        16620950911918289181 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__13_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        114, 101, 115, 111, 108, 118, 101, 80, 114, 111, 118, 105, 100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__13_value)
            as *mut leanh::LeanObject,
        5431388576214242839 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionOptions___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction_toJson___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 105, 116, 108, 101, 0],
};
static mut l_Lean_Lsp_instToJsonCodeAction_toJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction_toJson___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [107, 105, 110, 100, 0],
};
static mut l_Lean_Lsp_instToJsonCodeAction_toJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction_toJson___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 115, 80, 114, 101, 102, 101, 114, 114, 101, 100, 0],
};
static mut l_Lean_Lsp_instToJsonCodeAction_toJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction_toJson___closed__3_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 105, 115, 97, 98, 108, 101, 100, 0],
};
static mut l_Lean_Lsp_instToJsonCodeAction_toJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction_toJson___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 100, 105, 116, 0],
};
static mut l_Lean_Lsp_instToJsonCodeAction_toJson___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction_toJson___closed__5_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Lsp_instToJsonCodeAction_toJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeAction___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Lsp_instToJsonCodeAction_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonCodeAction___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeAction: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3_spec__6___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2_spec__4___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0_spec__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        9411147765090761777 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeAction_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        14590743692222096379 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__12_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [107, 105, 110, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__12_value)
            as *mut leanh::LeanObject,
        13532862018704899050 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__17_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__17_value)
            as *mut leanh::LeanObject,
        17830108945719632169 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__22_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 115, 80, 114, 101, 102, 101, 114, 114, 101, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__22_value)
            as *mut leanh::LeanObject,
        6676093269138613548 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__27_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 105, 115, 97, 98, 108, 101, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__28_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__27_value)
            as *mut leanh::LeanObject,
        17338299207067933995 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__28_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__32_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 100, 105, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__33_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__32_value)
            as *mut leanh::LeanObject,
        13303459820742955256 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__34_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__35_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__36_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__37_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 109, 109, 97, 110, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__38_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__37_value)
            as *mut leanh::LeanObject,
        839404257400331726 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__38_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__40_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeAction___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Lsp_instFromJsonCodeAction_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonCodeAction___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeAction: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [118, 97, 108, 117, 101, 83, 101, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__1_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 76, 105, 116, 101, 114, 97, 108, 83, 117,
        112, 112, 111, 114, 116, 86, 97, 108, 117, 101, 83, 101, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__1_value) as *mut leanh::LeanObject,5817383785314238607 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11556951273480865733 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__5_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 75, 105, 110, 100, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__1_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 76, 105, 116, 101, 114, 97, 108, 83, 117,
        112, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        15121913009763749583 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        13205171339069424383 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionLiteralSupport___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionLiteralSupport: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupport___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionLiteralSupport___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionLiteralSupport_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionLiteralSupport___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionLiteralSupport___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionLiteralSupport: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionLiteralSupport___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__0_value:
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
        100, 121, 110, 97, 109, 105, 99, 82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__1_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 67, 108, 105, 101, 110, 116, 67, 97, 112,
        97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        14125756375450080804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__5_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        100, 121, 110, 97, 109, 105, 99, 82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110,
        63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__5_value
        ) as *mut leanh::LeanObject,
        65642802442055394 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__10_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        105, 115, 80, 114, 101, 102, 101, 114, 114, 101, 100, 83, 117, 112, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__11_value:
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
        105, 115, 80, 114, 101, 102, 101, 114, 114, 101, 100, 83, 117, 112, 112, 111, 114, 116, 63,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__12_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__11_value
        ) as *mut leanh::LeanObject,
        16307344923389268512 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__12_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__16_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        100, 105, 115, 97, 98, 108, 101, 100, 83, 117, 112, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__16_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__17_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        100, 105, 115, 97, 98, 108, 101, 100, 83, 117, 112, 112, 111, 114, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__17_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__18_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__17_value
        ) as *mut leanh::LeanObject,
        18319031683155043551 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__18_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__22_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 97, 116, 97, 83, 117, 112, 112, 111, 114, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__22:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__22_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__23_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 97, 116, 97, 83, 117, 112, 112, 111, 114, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__23:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__23_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__24_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__23_value
        ) as *mut leanh::LeanObject,
        1516176701887076294 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__24_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__28_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        104, 111, 110, 111, 114, 115, 67, 104, 97, 110, 103, 101, 65, 110, 110, 111, 116, 97, 116,
        105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__28_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__29_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        104, 111, 110, 111, 114, 115, 67, 104, 97, 110, 103, 101, 65, 110, 110, 111, 116, 97, 116,
        105, 111, 110, 115, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__29:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__29_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__30_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__29_value
        ) as *mut leanh::LeanObject,
        16001231373810176241 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__30:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__30_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__34_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 76, 105, 116, 101, 114, 97, 108, 83, 117,
        112, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__34_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__35_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
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
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 76, 105, 116, 101, 114, 97, 108, 83, 117,
        112, 112, 111, 114, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__35:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__35_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__36_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__35_value
        ) as *mut leanh::LeanObject,
        13448351204617872740 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__36:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__36_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__37_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__37:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__40_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        114, 101, 115, 111, 108, 118, 101, 83, 117, 112, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__40:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__40_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__41_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        114, 101, 115, 111, 108, 118, 101, 83, 117, 112, 112, 111, 114, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__41:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__41_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__42_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__41_value
        ) as *mut leanh::LeanObject,
        10412173461716759590 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__42:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__42_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__43_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__43:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__44_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__44:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__45_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCodeActionClientCapabilities___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCodeActionClientCapabilities: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCodeActionClientCapabilities___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCodeActionClientCapabilities___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionClientCapabilities___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCodeActionClientCapabilities: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCodeActionClientCapabilities___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_ctorIdx(
    mut v_x_2978_: u8,
) -> *mut leanh::LeanObject {
    if v_x_2978_ == 0 {
        let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2979_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2979_;
    } else {
        let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2980_ = leanh::lean_unsigned_to_nat(1);
        return v___x_2980_;
    }
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_ctorIdx___boxed(
    mut v_x_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2982_: u8 = 0;
    let mut v_res_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2982_ = (leanh::lean_unbox(v_x_2981_) as u8);
    v_res_2983_ = l_Lean_Lsp_CodeActionTriggerKind_ctorIdx(v_x_boxed_2982_);
    return v_res_2983_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_toCtorIdx(
    mut v_x_2984_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2985_ = l_Lean_Lsp_CodeActionTriggerKind_ctorIdx(v_x_2984_);
    return v___x_2985_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_toCtorIdx___boxed(
    mut v_x_2986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_2987_: u8 = 0;
    let mut v_res_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2987_ = (leanh::lean_unbox(v_x_2986_) as u8);
    v_res_2988_ = l_Lean_Lsp_CodeActionTriggerKind_toCtorIdx(v_x_4__boxed_2987_);
    return v_res_2988_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_ctorElim___redArg(
    mut v_k_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2989_);
    return v_k_2989_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_ctorElim___redArg___boxed(
    mut v_k_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2991_ = l_Lean_Lsp_CodeActionTriggerKind_ctorElim___redArg(v_k_2990_);
    leanh::lean_dec(v_k_2990_);
    return v_res_2991_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_ctorElim(
    mut v_motive_2992_: *mut leanh::LeanObject,
    mut v_ctorIdx_2993_: *mut leanh::LeanObject,
    mut v_t_2994_: u8,
    mut v_h_2995_: *mut leanh::LeanObject,
    mut v_k_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2996_);
    return v_k_2996_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_ctorElim___boxed(
    mut v_motive_2997_: *mut leanh::LeanObject,
    mut v_ctorIdx_2998_: *mut leanh::LeanObject,
    mut v_t_2999_: *mut leanh::LeanObject,
    mut v_h_3000_: *mut leanh::LeanObject,
    mut v_k_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3002_: u8 = 0;
    let mut v_res_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3002_ = (leanh::lean_unbox(v_t_2999_) as u8);
    v_res_3003_ = l_Lean_Lsp_CodeActionTriggerKind_ctorElim(
        v_motive_2997_,
        v_ctorIdx_2998_,
        v_t_boxed_3002_,
        v_h_3000_,
        v_k_3001_,
    );
    leanh::lean_dec(v_k_3001_);
    leanh::lean_dec(v_ctorIdx_2998_);
    return v_res_3003_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_invoked_elim___redArg(
    mut v_invoked_3004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_invoked_3004_);
    return v_invoked_3004_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_invoked_elim___redArg___boxed(
    mut v_invoked_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Lean_Lsp_CodeActionTriggerKind_invoked_elim___redArg(v_invoked_3005_);
    leanh::lean_dec(v_invoked_3005_);
    return v_res_3006_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_invoked_elim(
    mut v_motive_3007_: *mut leanh::LeanObject,
    mut v_t_3008_: u8,
    mut v_h_3009_: *mut leanh::LeanObject,
    mut v_invoked_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_invoked_3010_);
    return v_invoked_3010_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_invoked_elim___boxed(
    mut v_motive_3011_: *mut leanh::LeanObject,
    mut v_t_3012_: *mut leanh::LeanObject,
    mut v_h_3013_: *mut leanh::LeanObject,
    mut v_invoked_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3015_: u8 = 0;
    let mut v_res_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3015_ = (leanh::lean_unbox(v_t_3012_) as u8);
    v_res_3016_ = l_Lean_Lsp_CodeActionTriggerKind_invoked_elim(
        v_motive_3011_,
        v_t_boxed_3015_,
        v_h_3013_,
        v_invoked_3014_,
    );
    leanh::lean_dec(v_invoked_3014_);
    return v_res_3016_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_automatic_elim___redArg(
    mut v_automatic_3017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_automatic_3017_);
    return v_automatic_3017_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_automatic_elim___redArg___boxed(
    mut v_automatic_3018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3019_ = l_Lean_Lsp_CodeActionTriggerKind_automatic_elim___redArg(v_automatic_3018_);
    leanh::lean_dec(v_automatic_3018_);
    return v_res_3019_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_automatic_elim(
    mut v_motive_3020_: *mut leanh::LeanObject,
    mut v_t_3021_: u8,
    mut v_h_3022_: *mut leanh::LeanObject,
    mut v_automatic_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_automatic_3023_);
    return v_automatic_3023_;
}
pub unsafe fn l_Lean_Lsp_CodeActionTriggerKind_automatic_elim___boxed(
    mut v_motive_3024_: *mut leanh::LeanObject,
    mut v_t_3025_: *mut leanh::LeanObject,
    mut v_h_3026_: *mut leanh::LeanObject,
    mut v_automatic_3027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3028_: u8 = 0;
    let mut v_res_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3028_ = (leanh::lean_unbox(v_t_3025_) as u8);
    v_res_3029_ = l_Lean_Lsp_CodeActionTriggerKind_automatic_elim(
        v_motive_3024_,
        v_t_boxed_3028_,
        v_h_3026_,
        v_automatic_3027_,
    );
    leanh::lean_dec(v_automatic_3027_);
    return v_res_3029_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = leanh::lean_unsigned_to_nat(1);
    v___x_3031_ = l_Lean_JsonNumber_fromNat(v___x_3030_);
    return v___x_3031_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__0_once
        ),
        _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__0,
    );
    v___x_3033_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3033_, 0, v___x_3032_);
    return v___x_3033_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3034_ = leanh::lean_unsigned_to_nat(2);
    v___x_3035_ = l_Lean_JsonNumber_fromNat(v___x_3034_);
    return v___x_3035_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__2_once
        ),
        _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__2,
    );
    v___x_3037_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3037_, 0, v___x_3036_);
    return v___x_3037_;
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0(
    mut v_x_3038_: u8,
) -> *mut leanh::LeanObject {
    if v_x_3038_ == 0 {
        let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3039_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1_once
            ),
            _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1,
        );
        return v___x_3039_;
    } else {
        let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3040_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3_once
            ),
            _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3,
        );
        return v___x_3040_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___boxed(
    mut v_x_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_56__boxed_3042_: u8 = 0;
    let mut v_res_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_56__boxed_3042_ = (leanh::lean_unbox(v_x_3041_) as u8);
    v_res_3043_ = l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0(v_x_56__boxed_3042_);
    return v_res_3043_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0(
    mut v_j_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_a_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3054_ = l_Lean_Json_getNat_x3f(v_j_3053_);
                if leanh::lean_obj_tag(v___x_3054_) == 0 {
                    v_a_3055_ = leanh::lean_ctor_get(v___x_3054_, 0);
                    v_isSharedCheck_3062_ = (!leanh::lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3062_ == 0 {
                        v___x_3057_ = v___x_3054_;
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3055_);
                        leanh::lean_dec(v___x_3054_);
                        v___x_3057_ = leanh::lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3063_ = leanh::lean_ctor_get(v___x_3054_, 0);
                    v_isSharedCheck_3079_ = (!leanh::lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3079_ == 0 {
                        v___x_3065_ = v___x_3054_;
                        v_isShared_3066_ = v_isSharedCheck_3079_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3063_);
                        leanh::lean_dec(v___x_3054_);
                        v___x_3065_ = leanh::lean_box(0);
                        v_isShared_3066_ = v_isSharedCheck_3079_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3060_;
            }
            3 => {
                v___x_3067_ = leanh::lean_unsigned_to_nat(1);
                v___x_3068_ = lean_nat_dec_eq(v_a_3063_, v___x_3067_);
                if v___x_3068_ == 0 {
                    v___x_3069_ = leanh::lean_unsigned_to_nat(2);
                    v___x_3070_ = lean_nat_dec_eq(v_a_3063_, v___x_3069_);
                    if v___x_3070_ == 0 {
                        v___x_3071_ =
                            l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__0;
                        v___x_3072_ = l_Nat_reprFast(v_a_3063_);
                        v___x_3073_ = lean_string_append(v___x_3071_, v___x_3072_);
                        leanh::lean_dec_ref(v___x_3072_);
                        if v_isShared_3066_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3065_, 0);
                            leanh::lean_ctor_set(v___x_3065_, 0, v___x_3073_);
                            v___x_3075_ = v___x_3065_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3076_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
                            v___x_3075_ = v_reuseFailAlloc_3076_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3065_);
                        leanh::lean_dec(v_a_3063_);
                        v___x_3077_ =
                            l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__1;
                        return v___x_3077_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3065_);
                    leanh::lean_dec(v_a_3063_);
                    v___x_3078_ = l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__2;
                    return v___x_3078_;
                }
            }
            4 => {
                return v___x_3075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5_spec__19(
    mut v_sz_3082_: usize,
    mut v_i_3083_: usize,
    mut v_bs_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut v_a_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3085_ = lean_usize_dec_lt(v_i_3083_, v_sz_3082_);
                if v___x_3085_ == 0 {
                    v___x_3086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3086_, 0, v_bs_3084_);
                    return v___x_3086_;
                } else {
                    v_v_3087_ = lean_array_uget_borrowed(v_bs_3084_, v_i_3083_);
                    leanh::lean_inc(v_v_3087_);
                    v___x_3088_ = l_Lean_Json_getStr_x3f(v_v_3087_);
                    if leanh::lean_obj_tag(v___x_3088_) == 0 {
                        leanh::lean_dec_ref(v_bs_3084_);
                        v_a_3089_ = leanh::lean_ctor_get(v___x_3088_, 0);
                        v_isSharedCheck_3096_ =
                            (!leanh::lean_is_exclusive(v___x_3088_)) as u8;
                        if v_isSharedCheck_3096_ == 0 {
                            v___x_3091_ = v___x_3088_;
                            v_isShared_3092_ = v_isSharedCheck_3096_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3089_);
                            leanh::lean_dec(v___x_3088_);
                            v___x_3091_ = leanh::lean_box(0);
                            v_isShared_3092_ = v_isSharedCheck_3096_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3097_ = leanh::lean_ctor_get(v___x_3088_, 0);
                        leanh::lean_inc(v_a_3097_);
                        leanh::lean_dec_ref_known(v___x_3088_, 1);
                        v___x_3098_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3099_ = lean_array_uset(v_bs_3084_, v_i_3083_, v___x_3098_);
                        v___x_3100_ = 1usize;
                        v___x_3101_ = lean_usize_add(v_i_3083_, v___x_3100_);
                        v___x_3102_ = lean_array_uset(v_bs_x27_3099_, v_i_3083_, v_a_3097_);
                        v_i_3083_ = v___x_3101_;
                        v_bs_3084_ = v___x_3102_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3092_ == 0 {
                    v___x_3094_ = v___x_3091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
                    v___x_3094_ = v_reuseFailAlloc_3095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5_spec__19___boxed(
    mut v_sz_3104_: *mut leanh::LeanObject,
    mut v_i_3105_: *mut leanh::LeanObject,
    mut v_bs_3106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3107_: usize = 0;
    let mut v_i_boxed_3108_: usize = 0;
    let mut v_res_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3107_ = leanh::lean_unbox_usize(v_sz_3104_);
    leanh::lean_dec(v_sz_3104_);
    v_i_boxed_3108_ = leanh::lean_unbox_usize(v_i_3105_);
    leanh::lean_dec(v_i_3105_);
    v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5_spec__19(v_sz_boxed_3107_, v_i_boxed_3108_, v_bs_3106_);
    return v_res_3109_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5(
    mut v_x_3112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3112_) == 4 {
        let mut v_elems_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3114_: usize = 0;
        let mut v___x_3115_: usize = 0;
        let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_3113_ = leanh::lean_ctor_get(v_x_3112_, 0);
        leanh::lean_inc_ref(v_elems_3113_);
        leanh::lean_dec_ref_known(v_x_3112_, 1);
        v_sz_3114_ = lean_array_size(v_elems_3113_);
        v___x_3115_ = 0usize;
        v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5_spec__19(v_sz_3114_, v___x_3115_, v_elems_3113_);
        return v___x_3116_;
    } else {
        let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3117_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0;
        v___x_3118_ = leanh::lean_unsigned_to_nat(80);
        v___x_3119_ = l_Lean_Json_pretty(v_x_3112_, v___x_3118_);
        v___x_3120_ = lean_string_append(v___x_3117_, v___x_3119_);
        leanh::lean_dec_ref(v___x_3119_);
        v___x_3121_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
        v___x_3122_ = lean_string_append(v___x_3120_, v___x_3121_);
        v___x_3123_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3123_, 0, v___x_3122_);
        return v___x_3123_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2(
    mut v_x_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3132_: u8 = 0;
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_a_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3140_: u8 = 0;
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3126_) == 0 {
                    v___x_3127_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2___closed__0;
                    return v___x_3127_;
                } else {
                    v___x_3128_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5(v_x_3126_);
                    if leanh::lean_obj_tag(v___x_3128_) == 0 {
                        v_a_3129_ = leanh::lean_ctor_get(v___x_3128_, 0);
                        v_isSharedCheck_3136_ =
                            (!leanh::lean_is_exclusive(v___x_3128_)) as u8;
                        if v_isSharedCheck_3136_ == 0 {
                            v___x_3131_ = v___x_3128_;
                            v_isShared_3132_ = v_isSharedCheck_3136_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3129_);
                            leanh::lean_dec(v___x_3128_);
                            v___x_3131_ = leanh::lean_box(0);
                            v_isShared_3132_ = v_isSharedCheck_3136_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3137_ = leanh::lean_ctor_get(v___x_3128_, 0);
                        v_isSharedCheck_3145_ =
                            (!leanh::lean_is_exclusive(v___x_3128_)) as u8;
                        if v_isSharedCheck_3145_ == 0 {
                            v___x_3139_ = v___x_3128_;
                            v_isShared_3140_ = v_isSharedCheck_3145_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3137_);
                            leanh::lean_dec(v___x_3128_);
                            v___x_3139_ = leanh::lean_box(0);
                            v_isShared_3140_ = v_isSharedCheck_3145_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3132_ == 0 {
                    v___x_3134_ = v___x_3131_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
                    v___x_3134_ = v_reuseFailAlloc_3135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3134_;
            }
            3 => {
                v___x_3141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3141_, 0, v_a_3137_);
                if v_isShared_3140_ == 0 {
                    leanh::lean_ctor_set(v___x_3139_, 0, v___x_3141_);
                    v___x_3143_ = v___x_3139_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3144_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
                    v___x_3143_ = v_reuseFailAlloc_3144_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1(
    mut v_j_3146_: *mut leanh::LeanObject,
    mut v_k_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3148_ = l_Lean_Json_getObjValD(v_j_3146_, v_k_3147_);
    v___x_3149_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2(v___x_3148_);
    return v___x_3149_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1___boxed(
    mut v_j_3150_: *mut leanh::LeanObject,
    mut v_k_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1(v_j_3150_, v_k_3151_);
    leanh::lean_dec_ref(v_k_3151_);
    return v_res_3152_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2_spec__4(
    mut v_x_3155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3157_: u8 = 0;
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3170_: u8 = 0;
    let mut v_a_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u8 = 0;
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: u8 = 0;
    let mut v_isSharedCheck_3187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3155_) == 0 {
                    v___x_3161_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2_spec__4___closed__0;
                    return v___x_3161_;
                } else {
                    v___x_3162_ = l_Lean_Json_getNat_x3f(v_x_3155_);
                    if leanh::lean_obj_tag(v___x_3162_) == 0 {
                        v_a_3163_ = leanh::lean_ctor_get(v___x_3162_, 0);
                        v_isSharedCheck_3170_ =
                            (!leanh::lean_is_exclusive(v___x_3162_)) as u8;
                        if v_isSharedCheck_3170_ == 0 {
                            v___x_3165_ = v___x_3162_;
                            v_isShared_3166_ = v_isSharedCheck_3170_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3163_);
                            leanh::lean_dec(v___x_3162_);
                            v___x_3165_ = leanh::lean_box(0);
                            v_isShared_3166_ = v_isSharedCheck_3170_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3171_ = leanh::lean_ctor_get(v___x_3162_, 0);
                        v_isSharedCheck_3187_ =
                            (!leanh::lean_is_exclusive(v___x_3162_)) as u8;
                        if v_isSharedCheck_3187_ == 0 {
                            v___x_3173_ = v___x_3162_;
                            v_isShared_3174_ = v_isSharedCheck_3187_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3171_);
                            leanh::lean_dec(v___x_3162_);
                            v___x_3173_ = leanh::lean_box(0);
                            v_isShared_3174_ = v_isSharedCheck_3187_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3158_ = leanh::lean_box((v_a_3157_) as usize);
                v___x_3159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3159_, 0, v___x_3158_);
                v___x_3160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3160_, 0, v___x_3159_);
                return v___x_3160_;
            }
            2 => {
                if v_isShared_3166_ == 0 {
                    v___x_3168_ = v___x_3165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
                    v___x_3168_ = v_reuseFailAlloc_3169_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3168_;
            }
            4 => {
                v___x_3175_ = leanh::lean_unsigned_to_nat(1);
                v___x_3176_ = lean_nat_dec_eq(v_a_3171_, v___x_3175_);
                if v___x_3176_ == 0 {
                    v___x_3177_ = leanh::lean_unsigned_to_nat(2);
                    v___x_3178_ = lean_nat_dec_eq(v_a_3171_, v___x_3177_);
                    if v___x_3178_ == 0 {
                        v___x_3179_ =
                            l_Lean_Lsp_instFromJsonCodeActionTriggerKind___lam__0___closed__0;
                        v___x_3180_ = l_Nat_reprFast(v_a_3171_);
                        v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
                        leanh::lean_dec_ref(v___x_3180_);
                        if v_isShared_3174_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3173_, 0);
                            leanh::lean_ctor_set(v___x_3173_, 0, v___x_3181_);
                            v___x_3183_ = v___x_3173_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3184_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
                            v___x_3183_ = v_reuseFailAlloc_3184_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3173_);
                        leanh::lean_dec(v_a_3171_);
                        v___x_3185_ = 1;
                        v_a_3157_ = v___x_3185_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3173_);
                    leanh::lean_dec(v_a_3171_);
                    v___x_3186_ = 0;
                    v_a_3157_ = v___x_3186_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                return v___x_3183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2(
    mut v_j_3188_: *mut leanh::LeanObject,
    mut v_k_3189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Lean_Json_getObjValD(v_j_3188_, v_k_3189_);
    v___x_3191_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2_spec__4(v___x_3190_);
    return v___x_3191_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2___boxed(
    mut v_j_3192_: *mut leanh::LeanObject,
    mut v_k_3193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3194_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2(v_j_3192_, v_k_3193_);
    leanh::lean_dec_ref(v_k_3193_);
    return v_res_3194_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16(
    mut v_x_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut v_a_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3197_) == 0 {
                    v___x_3198_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16___closed__0;
                    return v___x_3198_;
                } else {
                    v___x_3199_ = l_Lean_Json_getStr_x3f(v_x_3197_);
                    if leanh::lean_obj_tag(v___x_3199_) == 0 {
                        v_a_3200_ = leanh::lean_ctor_get(v___x_3199_, 0);
                        v_isSharedCheck_3207_ =
                            (!leanh::lean_is_exclusive(v___x_3199_)) as u8;
                        if v_isSharedCheck_3207_ == 0 {
                            v___x_3202_ = v___x_3199_;
                            v_isShared_3203_ = v_isSharedCheck_3207_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3200_);
                            leanh::lean_dec(v___x_3199_);
                            v___x_3202_ = leanh::lean_box(0);
                            v_isShared_3203_ = v_isSharedCheck_3207_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3208_ = leanh::lean_ctor_get(v___x_3199_, 0);
                        v_isSharedCheck_3216_ =
                            (!leanh::lean_is_exclusive(v___x_3199_)) as u8;
                        if v_isSharedCheck_3216_ == 0 {
                            v___x_3210_ = v___x_3199_;
                            v_isShared_3211_ = v_isSharedCheck_3216_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3208_);
                            leanh::lean_dec(v___x_3199_);
                            v___x_3210_ = leanh::lean_box(0);
                            v_isShared_3211_ = v_isSharedCheck_3216_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3203_ == 0 {
                    v___x_3205_ = v___x_3202_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3206_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
                    v___x_3205_ = v_reuseFailAlloc_3206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3205_;
            }
            3 => {
                v___x_3212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3212_, 0, v_a_3208_);
                if v_isShared_3211_ == 0 {
                    leanh::lean_ctor_set(v___x_3210_, 0, v___x_3212_);
                    v___x_3214_ = v___x_3210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3215_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
                    v___x_3214_ = v_reuseFailAlloc_3215_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(
    mut v_j_3217_: *mut leanh::LeanObject,
    mut v_k_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3219_ = l_Lean_Json_getObjValD(v_j_3217_, v_k_3218_);
    v___x_3220_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16(v___x_3219_);
    return v___x_3220_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10___boxed(
    mut v_j_3221_: *mut leanh::LeanObject,
    mut v_k_3222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_j_3221_, v_k_3222_);
    leanh::lean_dec_ref(v_k_3222_);
    return v_res_3223_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__5(
    mut v_j_3224_: *mut leanh::LeanObject,
    mut v_k_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3226_ = l_Lean_Json_getObjValD(v_j_3224_, v_k_3225_);
    v___x_3227_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_3226_);
    return v___x_3227_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_j_3228_: *mut leanh::LeanObject,
    mut v_k_3229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3230_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__5(v_j_3228_, v_k_3229_);
    leanh::lean_dec_ref(v_k_3229_);
    return v_res_3230_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6_spec__8(
    mut v_x_3233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3243_: u8 = 0;
    let mut v_a_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3233_) == 0 {
                    v___x_3234_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6_spec__8___closed__0;
                    return v___x_3234_;
                } else {
                    v___x_3235_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_3233_);
                    if leanh::lean_obj_tag(v___x_3235_) == 0 {
                        v_a_3236_ = leanh::lean_ctor_get(v___x_3235_, 0);
                        v_isSharedCheck_3243_ =
                            (!leanh::lean_is_exclusive(v___x_3235_)) as u8;
                        if v_isSharedCheck_3243_ == 0 {
                            v___x_3238_ = v___x_3235_;
                            v_isShared_3239_ = v_isSharedCheck_3243_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3236_);
                            leanh::lean_dec(v___x_3235_);
                            v___x_3238_ = leanh::lean_box(0);
                            v_isShared_3239_ = v_isSharedCheck_3243_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3244_ = leanh::lean_ctor_get(v___x_3235_, 0);
                        v_isSharedCheck_3252_ =
                            (!leanh::lean_is_exclusive(v___x_3235_)) as u8;
                        if v_isSharedCheck_3252_ == 0 {
                            v___x_3246_ = v___x_3235_;
                            v_isShared_3247_ = v_isSharedCheck_3252_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3244_);
                            leanh::lean_dec(v___x_3235_);
                            v___x_3246_ = leanh::lean_box(0);
                            v_isShared_3247_ = v_isSharedCheck_3252_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3239_ == 0 {
                    v___x_3241_ = v___x_3238_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3242_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
                    v___x_3241_ = v_reuseFailAlloc_3242_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3241_;
            }
            3 => {
                v___x_3248_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3248_, 0, v_a_3244_);
                if v_isShared_3247_ == 0 {
                    leanh::lean_ctor_set(v___x_3246_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3246_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6(
    mut v_j_3253_: *mut leanh::LeanObject,
    mut v_k_3254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = l_Lean_Json_getObjValD(v_j_3253_, v_k_3254_);
    v___x_3256_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6_spec__8(v___x_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_j_3257_: *mut leanh::LeanObject,
    mut v_k_3258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3259_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6(v_j_3257_, v_k_3258_);
    leanh::lean_dec_ref(v_k_3258_);
    return v_res_3259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28(
    mut v_sz_3263_: usize,
    mut v_i_3264_: usize,
    mut v_bs_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3276_: u8 = 0;
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3268_ = lean_usize_dec_lt(v_i_3264_, v_sz_3263_);
                if v___x_3268_ == 0 {
                    v___x_3269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3269_, 0, v_bs_3265_);
                    return v___x_3269_;
                } else {
                    v_v_3270_ = lean_array_uget_borrowed(v_bs_3265_, v_i_3264_);
                    leanh::lean_inc(v_v_3270_);
                    v___x_3271_ = l_Lean_Json_getNat_x3f(v_v_3270_);
                    if leanh::lean_obj_tag(v___x_3271_) == 1 {
                        v_a_3272_ = leanh::lean_ctor_get(v___x_3271_, 0);
                        leanh::lean_inc(v_a_3272_);
                        leanh::lean_dec_ref_known(v___x_3271_, 1);
                        v___x_3273_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3274_ = lean_array_uset(v_bs_3265_, v_i_3264_, v___x_3273_);
                        v___x_3282_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3283_ = lean_nat_dec_eq(v_a_3272_, v___x_3282_);
                        if v___x_3283_ == 0 {
                            v___x_3284_ = leanh::lean_unsigned_to_nat(2);
                            v___x_3285_ = lean_nat_dec_eq(v_a_3272_, v___x_3284_);
                            leanh::lean_dec(v_a_3272_);
                            if v___x_3285_ == 0 {
                                leanh::lean_dec_ref(v_bs_x27_3274_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3286_ = 1;
                                v_a_3276_ = v___x_3286_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3272_);
                            v___x_3287_ = 0;
                            v_a_3276_ = v___x_3287_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3271_);
                        leanh::lean_dec_ref(v_bs_3265_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___closed__1;
                return v___x_3267_;
            }
            2 => {
                v___x_3277_ = 1usize;
                v___x_3278_ = lean_usize_add(v_i_3264_, v___x_3277_);
                v___x_3279_ = leanh::lean_box((v_a_3276_) as usize);
                v___x_3280_ = lean_array_uset(v_bs_x27_3274_, v_i_3264_, v___x_3279_);
                v_i_3264_ = v___x_3278_;
                v_bs_3265_ = v___x_3280_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28___boxed(
    mut v_sz_3288_: *mut leanh::LeanObject,
    mut v_i_3289_: *mut leanh::LeanObject,
    mut v_bs_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3291_: usize = 0;
    let mut v_i_boxed_3292_: usize = 0;
    let mut v_res_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3291_ = leanh::lean_unbox_usize(v_sz_3288_);
    leanh::lean_dec(v_sz_3288_);
    v_i_boxed_3292_ = leanh::lean_unbox_usize(v_i_3289_);
    leanh::lean_dec(v_i_3289_);
    v_res_3293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28(v_sz_boxed_3291_, v_i_boxed_3292_, v_bs_3290_);
    return v_res_3293_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22(
    mut v_x_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3294_) == 4 {
        let mut v_elems_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3296_: usize = 0;
        let mut v___x_3297_: usize = 0;
        let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_3295_ = leanh::lean_ctor_get(v_x_3294_, 0);
        leanh::lean_inc_ref(v_elems_3295_);
        leanh::lean_dec_ref_known(v_x_3294_, 1);
        v_sz_3296_ = lean_array_size(v_elems_3295_);
        v___x_3297_ = 0usize;
        v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22_spec__28(v_sz_3296_, v___x_3297_, v_elems_3295_);
        return v___x_3298_;
    } else {
        let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3299_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0;
        v___x_3300_ = leanh::lean_unsigned_to_nat(80);
        v___x_3301_ = l_Lean_Json_pretty(v_x_3294_, v___x_3300_);
        v___x_3302_ = lean_string_append(v___x_3299_, v___x_3301_);
        leanh::lean_dec_ref(v___x_3301_);
        v___x_3303_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
        v___x_3304_ = lean_string_append(v___x_3302_, v___x_3303_);
        v___x_3305_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3305_, 0, v___x_3304_);
        return v___x_3305_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19(
    mut v_x_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3314_: u8 = 0;
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v_a_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3308_) == 0 {
                    v___x_3309_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19___closed__0;
                    return v___x_3309_;
                } else {
                    v___x_3310_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19_spec__22(v_x_3308_);
                    if leanh::lean_obj_tag(v___x_3310_) == 0 {
                        v_a_3311_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        v_isSharedCheck_3318_ =
                            (!leanh::lean_is_exclusive(v___x_3310_)) as u8;
                        if v_isSharedCheck_3318_ == 0 {
                            v___x_3313_ = v___x_3310_;
                            v_isShared_3314_ = v_isSharedCheck_3318_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3311_);
                            leanh::lean_dec(v___x_3310_);
                            v___x_3313_ = leanh::lean_box(0);
                            v_isShared_3314_ = v_isSharedCheck_3318_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3319_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        v_isSharedCheck_3327_ =
                            (!leanh::lean_is_exclusive(v___x_3310_)) as u8;
                        if v_isSharedCheck_3327_ == 0 {
                            v___x_3321_ = v___x_3310_;
                            v_isShared_3322_ = v_isSharedCheck_3327_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3319_);
                            leanh::lean_dec(v___x_3310_);
                            v___x_3321_ = leanh::lean_box(0);
                            v_isShared_3322_ = v_isSharedCheck_3327_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3314_ == 0 {
                    v___x_3316_ = v___x_3313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
                    v___x_3316_ = v_reuseFailAlloc_3317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3316_;
            }
            3 => {
                v___x_3323_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3323_, 0, v_a_3319_);
                if v_isShared_3322_ == 0 {
                    leanh::lean_ctor_set(v___x_3321_, 0, v___x_3323_);
                    v___x_3325_ = v___x_3321_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12(
    mut v_j_3328_: *mut leanh::LeanObject,
    mut v_k_3329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Lean_Json_getObjValD(v_j_3328_, v_k_3329_);
    v___x_3331_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12_spec__19(v___x_3330_);
    return v___x_3331_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12___boxed(
    mut v_j_3332_: *mut leanh::LeanObject,
    mut v_k_3333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12(v_j_3332_, v_k_3333_);
    leanh::lean_dec_ref(v_k_3333_);
    return v_res_3334_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14(
    mut v_x_3338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3338_) == 0 {
                    v___x_3352_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__1;
                    return v___x_3352_;
                } else {
                    match leanh::lean_obj_tag(v_x_3338_) {
                        2 => {
                            v_n_3353_ = leanh::lean_ctor_get(v_x_3338_, 0);
                            v_mantissa_3354_ = leanh::lean_ctor_get(v_n_3353_, 0);
                            v_exponent_3355_ = leanh::lean_ctor_get(v_n_3353_, 1);
                            v___x_3356_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3357_ = lean_nat_dec_eq(v_exponent_3355_, v___x_3356_);
                            if v___x_3357_ == 0 {
                                v_j_3344_ = v_x_3338_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_mantissa_3354_);
                                leanh::lean_dec_ref_known(v_x_3338_, 1);
                                v___x_3358_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3358_, 0, v_mantissa_3354_);
                                v_a_3340_ = v___x_3358_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_s_3359_ = leanh::lean_ctor_get(v_x_3338_, 0);
                            leanh::lean_inc_ref(v_s_3359_);
                            leanh::lean_dec_ref_known(v_x_3338_, 1);
                            v___x_3360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3360_, 0, v_s_3359_);
                            v_a_3340_ = v___x_3360_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_j_3344_ = v_x_3338_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3341_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3341_, 0, v_a_3340_);
                v___x_3342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3342_, 0, v___x_3341_);
                return v___x_3342_;
            }
            2 => {
                v___x_3345_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14___closed__0;
                v___x_3346_ = leanh::lean_unsigned_to_nat(80);
                v___x_3347_ = l_Lean_Json_pretty(v_j_3344_, v___x_3346_);
                v___x_3348_ = lean_string_append(v___x_3345_, v___x_3347_);
                leanh::lean_dec_ref(v___x_3347_);
                v___x_3349_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
                v___x_3350_ = lean_string_append(v___x_3348_, v___x_3349_);
                v___x_3351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
                return v___x_3351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9(
    mut v_j_3361_: *mut leanh::LeanObject,
    mut v_k_3362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3363_ = l_Lean_Json_getObjValD(v_j_3361_, v_k_3362_);
    v___x_3364_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9_spec__14(v___x_3363_);
    return v___x_3364_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9___boxed(
    mut v_j_3365_: *mut leanh::LeanObject,
    mut v_k_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3367_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9(v_j_3365_, v_k_3366_);
    leanh::lean_dec_ref(v_k_3366_);
    return v_res_3367_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__11(
    mut v_j_3368_: *mut leanh::LeanObject,
    mut v_k_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = l_Lean_Json_getObjValD(v_j_3368_, v_k_3369_);
    v___x_3371_ = l_Lean_Json_getStr_x3f(v___x_3370_);
    return v___x_3371_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__11___boxed(
    mut v_j_3372_: *mut leanh::LeanObject,
    mut v_k_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3374_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__11(v_j_3372_, v_k_3373_);
    leanh::lean_dec_ref(v_k_3373_);
    return v_res_3374_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15_spec__25(
    mut v_x_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3377_) == 0 {
        let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3378_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15_spec__25___closed__0;
        return v___x_3378_;
    } else {
        let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3379_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3379_, 0, v_x_3377_);
        v___x_3380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3380_, 0, v___x_3379_);
        return v___x_3380_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15(
    mut v_j_3381_: *mut leanh::LeanObject,
    mut v_k_3382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = l_Lean_Json_getObjValD(v_j_3381_, v_k_3382_);
    v___x_3384_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15_spec__25(v___x_3383_);
    return v___x_3384_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15___boxed(
    mut v_j_3385_: *mut leanh::LeanObject,
    mut v_k_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15(v_j_3385_, v_k_3386_);
    leanh::lean_dec_ref(v_k_3386_);
    return v_res_3387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23_spec__28_spec__34(
    mut v_sz_3388_: usize,
    mut v_i_3389_: usize,
    mut v_bs_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_a_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: usize = 0;
    let mut v___x_3407_: usize = 0;
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3391_ = lean_usize_dec_lt(v_i_3389_, v_sz_3388_);
                if v___x_3391_ == 0 {
                    v___x_3392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3392_, 0, v_bs_3390_);
                    return v___x_3392_;
                } else {
                    v_v_3393_ = lean_array_uget_borrowed(v_bs_3390_, v_i_3389_);
                    leanh::lean_inc(v_v_3393_);
                    v___x_3394_ =
                        l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_3393_);
                    if leanh::lean_obj_tag(v___x_3394_) == 0 {
                        leanh::lean_dec_ref(v_bs_3390_);
                        v_a_3395_ = leanh::lean_ctor_get(v___x_3394_, 0);
                        v_isSharedCheck_3402_ =
                            (!leanh::lean_is_exclusive(v___x_3394_)) as u8;
                        if v_isSharedCheck_3402_ == 0 {
                            v___x_3397_ = v___x_3394_;
                            v_isShared_3398_ = v_isSharedCheck_3402_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3395_);
                            leanh::lean_dec(v___x_3394_);
                            v___x_3397_ = leanh::lean_box(0);
                            v_isShared_3398_ = v_isSharedCheck_3402_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3403_ = leanh::lean_ctor_get(v___x_3394_, 0);
                        leanh::lean_inc(v_a_3403_);
                        leanh::lean_dec_ref_known(v___x_3394_, 1);
                        v___x_3404_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3405_ = lean_array_uset(v_bs_3390_, v_i_3389_, v___x_3404_);
                        v___x_3406_ = 1usize;
                        v___x_3407_ = lean_usize_add(v_i_3389_, v___x_3406_);
                        v___x_3408_ = lean_array_uset(v_bs_x27_3405_, v_i_3389_, v_a_3403_);
                        v_i_3389_ = v___x_3407_;
                        v_bs_3390_ = v___x_3408_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3398_ == 0 {
                    v___x_3400_ = v___x_3397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
                    v___x_3400_ = v_reuseFailAlloc_3401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23_spec__28_spec__34___boxed(
    mut v_sz_3410_: *mut leanh::LeanObject,
    mut v_i_3411_: *mut leanh::LeanObject,
    mut v_bs_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3413_: usize = 0;
    let mut v_i_boxed_3414_: usize = 0;
    let mut v_res_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3413_ = leanh::lean_unbox_usize(v_sz_3410_);
    leanh::lean_dec(v_sz_3410_);
    v_i_boxed_3414_ = leanh::lean_unbox_usize(v_i_3411_);
    leanh::lean_dec(v_i_3411_);
    v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23_spec__28_spec__34(v_sz_boxed_3413_, v_i_boxed_3414_, v_bs_3412_);
    return v_res_3415_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23_spec__28(
    mut v_x_3416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3416_) == 4 {
        let mut v_elems_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3418_: usize = 0;
        let mut v___x_3419_: usize = 0;
        let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_3417_ = leanh::lean_ctor_get(v_x_3416_, 0);
        leanh::lean_inc_ref(v_elems_3417_);
        leanh::lean_dec_ref_known(v_x_3416_, 1);
        v_sz_3418_ = lean_array_size(v_elems_3417_);
        v___x_3419_ = 0usize;
        v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23_spec__28_spec__34(v_sz_3418_, v___x_3419_, v_elems_3417_);
        return v___x_3420_;
    } else {
        let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3421_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0;
        v___x_3422_ = leanh::lean_unsigned_to_nat(80);
        v___x_3423_ = l_Lean_Json_pretty(v_x_3416_, v___x_3422_);
        v___x_3424_ = lean_string_append(v___x_3421_, v___x_3423_);
        leanh::lean_dec_ref(v___x_3423_);
        v___x_3425_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
        v___x_3426_ = lean_string_append(v___x_3424_, v___x_3425_);
        v___x_3427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3427_, 0, v___x_3426_);
        return v___x_3427_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23(
    mut v_x_3430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut v_a_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3430_) == 0 {
                    v___x_3431_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23___closed__0;
                    return v___x_3431_;
                } else {
                    v___x_3432_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23_spec__28(v_x_3430_);
                    if leanh::lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3440_ =
                            (!leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3440_ == 0 {
                            v___x_3435_ = v___x_3432_;
                            v_isShared_3436_ = v_isSharedCheck_3440_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3433_);
                            leanh::lean_dec(v___x_3432_);
                            v___x_3435_ = leanh::lean_box(0);
                            v_isShared_3436_ = v_isSharedCheck_3440_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3441_ = leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3449_ =
                            (!leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3449_ == 0 {
                            v___x_3443_ = v___x_3432_;
                            v_isShared_3444_ = v_isSharedCheck_3449_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3441_);
                            leanh::lean_dec(v___x_3432_);
                            v___x_3443_ = leanh::lean_box(0);
                            v_isShared_3444_ = v_isSharedCheck_3449_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3436_ == 0 {
                    v___x_3438_ = v___x_3435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
                    v___x_3438_ = v_reuseFailAlloc_3439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3438_;
            }
            3 => {
                v___x_3445_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3445_, 0, v_a_3441_);
                if v_isShared_3444_ == 0 {
                    leanh::lean_ctor_set(v___x_3443_, 0, v___x_3445_);
                    v___x_3447_ = v___x_3443_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
                    v___x_3447_ = v_reuseFailAlloc_3448_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3447_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14(
    mut v_j_3450_: *mut leanh::LeanObject,
    mut v_k_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = l_Lean_Json_getObjValD(v_j_3450_, v_k_3451_);
    v___x_3453_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14_spec__23(v___x_3452_);
    return v___x_3453_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14___boxed(
    mut v_j_3454_: *mut leanh::LeanObject,
    mut v_k_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3456_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14(v_j_3454_, v_k_3455_);
    leanh::lean_dec_ref(v_k_3455_);
    return v_res_3456_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12(
    mut v_x_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3459_) == 0 {
                    v___x_3460_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12___closed__0;
                    return v___x_3460_;
                } else {
                    v___x_3461_ = l_Lean_Json_getBool_x3f(v_x_3459_);
                    if leanh::lean_obj_tag(v___x_3461_) == 0 {
                        v_a_3462_ = leanh::lean_ctor_get(v___x_3461_, 0);
                        v_isSharedCheck_3469_ =
                            (!leanh::lean_is_exclusive(v___x_3461_)) as u8;
                        if v_isSharedCheck_3469_ == 0 {
                            v___x_3464_ = v___x_3461_;
                            v_isShared_3465_ = v_isSharedCheck_3469_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3462_);
                            leanh::lean_dec(v___x_3461_);
                            v___x_3464_ = leanh::lean_box(0);
                            v_isShared_3465_ = v_isSharedCheck_3469_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3470_ = leanh::lean_ctor_get(v___x_3461_, 0);
                        v_isSharedCheck_3478_ =
                            (!leanh::lean_is_exclusive(v___x_3461_)) as u8;
                        if v_isSharedCheck_3478_ == 0 {
                            v___x_3472_ = v___x_3461_;
                            v_isShared_3473_ = v_isSharedCheck_3478_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3470_);
                            leanh::lean_dec(v___x_3461_);
                            v___x_3472_ = leanh::lean_box(0);
                            v_isShared_3473_ = v_isSharedCheck_3478_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3465_ == 0 {
                    v___x_3467_ = v___x_3464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3467_;
            }
            3 => {
                v___x_3474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3474_, 0, v_a_3470_);
                if v_isShared_3473_ == 0 {
                    leanh::lean_ctor_set(v___x_3472_, 0, v___x_3474_);
                    v___x_3476_ = v___x_3472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12___boxed(
    mut v_x_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12(v_x_3479_);
    leanh::lean_dec(v_x_3479_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(
    mut v_j_3481_: *mut leanh::LeanObject,
    mut v_k_3482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_Json_getObjValD(v_j_3481_, v_k_3482_);
    v___x_3484_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8_spec__12(v___x_3483_);
    leanh::lean_dec(v___x_3483_);
    return v___x_3484_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8___boxed(
    mut v_j_3485_: *mut leanh::LeanObject,
    mut v_k_3486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_j_3485_, v_k_3486_);
    leanh::lean_dec_ref(v_k_3486_);
    return v_res_3487_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31(
    mut v_sz_3491_: usize,
    mut v_i_3492_: usize,
    mut v_bs_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3504_: u8 = 0;
    let mut v___x_3505_: usize = 0;
    let mut v___x_3506_: usize = 0;
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: u8 = 0;
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3515_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ = lean_usize_dec_lt(v_i_3492_, v_sz_3491_);
                if v___x_3496_ == 0 {
                    v___x_3497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3497_, 0, v_bs_3493_);
                    return v___x_3497_;
                } else {
                    v_v_3498_ = lean_array_uget_borrowed(v_bs_3493_, v_i_3492_);
                    leanh::lean_inc(v_v_3498_);
                    v___x_3499_ = l_Lean_Json_getNat_x3f(v_v_3498_);
                    if leanh::lean_obj_tag(v___x_3499_) == 1 {
                        v_a_3500_ = leanh::lean_ctor_get(v___x_3499_, 0);
                        leanh::lean_inc(v_a_3500_);
                        leanh::lean_dec_ref_known(v___x_3499_, 1);
                        v___x_3501_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3502_ = lean_array_uset(v_bs_3493_, v_i_3492_, v___x_3501_);
                        v___x_3510_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3511_ = lean_nat_dec_eq(v_a_3500_, v___x_3510_);
                        if v___x_3511_ == 0 {
                            v___x_3512_ = leanh::lean_unsigned_to_nat(2);
                            v___x_3513_ = lean_nat_dec_eq(v_a_3500_, v___x_3512_);
                            leanh::lean_dec(v_a_3500_);
                            if v___x_3513_ == 0 {
                                leanh::lean_dec_ref(v_bs_x27_3502_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3514_ = 1;
                                v_a_3504_ = v___x_3514_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3500_);
                            v___x_3515_ = 0;
                            v_a_3504_ = v___x_3515_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3499_);
                        leanh::lean_dec_ref(v_bs_3493_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___closed__1;
                return v___x_3495_;
            }
            2 => {
                v___x_3505_ = 1usize;
                v___x_3506_ = lean_usize_add(v_i_3492_, v___x_3505_);
                v___x_3507_ = leanh::lean_box((v_a_3504_) as usize);
                v___x_3508_ = lean_array_uset(v_bs_x27_3502_, v_i_3492_, v___x_3507_);
                v_i_3492_ = v___x_3506_;
                v_bs_3493_ = v___x_3508_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31___boxed(
    mut v_sz_3516_: *mut leanh::LeanObject,
    mut v_i_3517_: *mut leanh::LeanObject,
    mut v_bs_3518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3519_: usize = 0;
    let mut v_i_boxed_3520_: usize = 0;
    let mut v_res_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3519_ = leanh::lean_unbox_usize(v_sz_3516_);
    leanh::lean_dec(v_sz_3516_);
    v_i_boxed_3520_ = leanh::lean_unbox_usize(v_i_3517_);
    leanh::lean_dec(v_i_3517_);
    v_res_3521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31(v_sz_boxed_3519_, v_i_boxed_3520_, v_bs_3518_);
    return v_res_3521_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25(
    mut v_x_3522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3522_) == 4 {
        let mut v_elems_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3524_: usize = 0;
        let mut v___x_3525_: usize = 0;
        let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_3523_ = leanh::lean_ctor_get(v_x_3522_, 0);
        leanh::lean_inc_ref(v_elems_3523_);
        leanh::lean_dec_ref_known(v_x_3522_, 1);
        v_sz_3524_ = lean_array_size(v_elems_3523_);
        v___x_3525_ = 0usize;
        v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25_spec__31(v_sz_3524_, v___x_3525_, v_elems_3523_);
        return v___x_3526_;
    } else {
        let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3527_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0;
        v___x_3528_ = leanh::lean_unsigned_to_nat(80);
        v___x_3529_ = l_Lean_Json_pretty(v_x_3522_, v___x_3528_);
        v___x_3530_ = lean_string_append(v___x_3527_, v___x_3529_);
        leanh::lean_dec_ref(v___x_3529_);
        v___x_3531_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
        v___x_3532_ = lean_string_append(v___x_3530_, v___x_3531_);
        v___x_3533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3533_, 0, v___x_3532_);
        return v___x_3533_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21(
    mut v_x_3536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3542_: u8 = 0;
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3546_: u8 = 0;
    let mut v_a_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3536_) == 0 {
                    v___x_3537_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21___closed__0;
                    return v___x_3537_;
                } else {
                    v___x_3538_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21_spec__25(v_x_3536_);
                    if leanh::lean_obj_tag(v___x_3538_) == 0 {
                        v_a_3539_ = leanh::lean_ctor_get(v___x_3538_, 0);
                        v_isSharedCheck_3546_ =
                            (!leanh::lean_is_exclusive(v___x_3538_)) as u8;
                        if v_isSharedCheck_3546_ == 0 {
                            v___x_3541_ = v___x_3538_;
                            v_isShared_3542_ = v_isSharedCheck_3546_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3539_);
                            leanh::lean_dec(v___x_3538_);
                            v___x_3541_ = leanh::lean_box(0);
                            v_isShared_3542_ = v_isSharedCheck_3546_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3547_ = leanh::lean_ctor_get(v___x_3538_, 0);
                        v_isSharedCheck_3555_ =
                            (!leanh::lean_is_exclusive(v___x_3538_)) as u8;
                        if v_isSharedCheck_3555_ == 0 {
                            v___x_3549_ = v___x_3538_;
                            v_isShared_3550_ = v_isSharedCheck_3555_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3547_);
                            leanh::lean_dec(v___x_3538_);
                            v___x_3549_ = leanh::lean_box(0);
                            v_isShared_3550_ = v_isSharedCheck_3555_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3542_ == 0 {
                    v___x_3544_ = v___x_3541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
                    v___x_3544_ = v_reuseFailAlloc_3545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3544_;
            }
            3 => {
                v___x_3551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3551_, 0, v_a_3547_);
                if v_isShared_3550_ == 0 {
                    leanh::lean_ctor_set(v___x_3549_, 0, v___x_3551_);
                    v___x_3553_ = v___x_3549_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
                    v___x_3553_ = v_reuseFailAlloc_3554_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13(
    mut v_j_3556_: *mut leanh::LeanObject,
    mut v_k_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_Json_getObjValD(v_j_3556_, v_k_3557_);
    v___x_3559_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13_spec__21(v___x_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13___boxed(
    mut v_j_3560_: *mut leanh::LeanObject,
    mut v_k_3561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13(v_j_3560_, v_k_3561_);
    leanh::lean_dec_ref(v_k_3561_);
    return v_res_3562_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10(
    mut v_x_3566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3576_: u8 = 0;
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3566_) == 0 {
                    v___x_3580_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__1;
                    return v___x_3580_;
                } else {
                    leanh::lean_inc(v_x_3566_);
                    v___x_3581_ = l_Lean_Json_getNat_x3f(v_x_3566_);
                    if leanh::lean_obj_tag(v___x_3581_) == 1 {
                        v_a_3582_ = leanh::lean_ctor_get(v___x_3581_, 0);
                        leanh::lean_inc(v_a_3582_);
                        leanh::lean_dec_ref_known(v___x_3581_, 1);
                        v___x_3583_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3584_ = lean_nat_dec_eq(v_a_3582_, v___x_3583_);
                        if v___x_3584_ == 0 {
                            v___x_3585_ = leanh::lean_unsigned_to_nat(2);
                            v___x_3586_ = lean_nat_dec_eq(v_a_3582_, v___x_3585_);
                            if v___x_3586_ == 0 {
                                v___x_3587_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3588_ = lean_nat_dec_eq(v_a_3582_, v___x_3587_);
                                if v___x_3588_ == 0 {
                                    v___x_3589_ = leanh::lean_unsigned_to_nat(4);
                                    v___x_3590_ = lean_nat_dec_eq(v_a_3582_, v___x_3589_);
                                    leanh::lean_dec(v_a_3582_);
                                    if v___x_3590_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_x_3566_);
                                        v___x_3591_ = 3;
                                        v_a_3576_ = v___x_3591_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3582_);
                                    leanh::lean_dec(v_x_3566_);
                                    v___x_3592_ = 2;
                                    v_a_3576_ = v___x_3592_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_3582_);
                                leanh::lean_dec(v_x_3566_);
                                v___x_3593_ = 1;
                                v_a_3576_ = v___x_3593_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3582_);
                            leanh::lean_dec(v_x_3566_);
                            v___x_3594_ = 0;
                            v_a_3576_ = v___x_3594_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3581_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3568_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10___closed__0;
                v___x_3569_ = leanh::lean_unsigned_to_nat(80);
                v___x_3570_ = l_Lean_Json_pretty(v_x_3566_, v___x_3569_);
                v___x_3571_ = lean_string_append(v___x_3568_, v___x_3570_);
                leanh::lean_dec_ref(v___x_3570_);
                v___x_3572_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
                v___x_3573_ = lean_string_append(v___x_3571_, v___x_3572_);
                v___x_3574_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3574_, 0, v___x_3573_);
                return v___x_3574_;
            }
            2 => {
                v___x_3577_ = leanh::lean_box((v_a_3576_) as usize);
                v___x_3578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3578_, 0, v___x_3577_);
                v___x_3579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                return v___x_3579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7(
    mut v_j_3595_: *mut leanh::LeanObject,
    mut v_k_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3597_ = l_Lean_Json_getObjValD(v_j_3595_, v_k_3596_);
    v___x_3598_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7_spec__10(v___x_3597_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7___boxed(
    mut v_j_3599_: *mut leanh::LeanObject,
    mut v_k_3600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3601_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7(v_j_3599_, v_k_3600_);
    leanh::lean_dec_ref(v_k_3600_);
    return v_res_3601_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ = 1;
    v___x_3611_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__4;
    v___x_3612_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3611_, v___x_3610_);
    return v___x_3612_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_3615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__5);
    v___x_3616_ = lean_string_append(v___x_3615_, v___x_3614_);
    return v___x_3616_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3619_: u8 = 0;
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = 1;
    v___x_3620_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__8;
    v___x_3621_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3620_, v___x_3619_);
    return v___x_3621_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9);
    v___x_3623_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3624_ = lean_string_append(v___x_3623_, v___x_3622_);
    return v___x_3624_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3627_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__10), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__10_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__10);
    v___x_3628_ = lean_string_append(v___x_3627_, v___x_3626_);
    return v___x_3628_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3633_ = 1;
    v___x_3634_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__15;
    v___x_3635_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3634_, v___x_3633_);
    return v___x_3635_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3636_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__16), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__16_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__16);
    v___x_3637_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3638_ = lean_string_append(v___x_3637_, v___x_3636_);
    return v___x_3638_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3639_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3640_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__17_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__17);
    v___x_3641_ = lean_string_append(v___x_3640_, v___x_3639_);
    return v___x_3641_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = 1;
    v___x_3647_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__21;
    v___x_3648_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3647_, v___x_3646_);
    return v___x_3648_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3649_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__22), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__22_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__22);
    v___x_3650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3651_ = lean_string_append(v___x_3650_, v___x_3649_);
    return v___x_3651_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3652_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__23), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__23_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__23);
    v___x_3654_ = lean_string_append(v___x_3653_, v___x_3652_);
    return v___x_3654_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = 1;
    v___x_3660_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__27;
    v___x_3661_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3660_, v___x_3659_);
    return v___x_3661_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3662_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__28), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__28_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__28);
    v___x_3663_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3664_ = lean_string_append(v___x_3663_, v___x_3662_);
    return v___x_3664_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3666_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__29_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__29);
    v___x_3667_ = lean_string_append(v___x_3666_, v___x_3665_);
    return v___x_3667_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_3672_: u8 = 0;
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = 1;
    v___x_3673_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__33;
    v___x_3674_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3673_, v___x_3672_);
    return v___x_3674_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__34), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__34_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__34);
    v___x_3676_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3677_ = lean_string_append(v___x_3676_, v___x_3675_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__35), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__35_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__35);
    v___x_3680_ = lean_string_append(v___x_3679_, v___x_3678_);
    return v___x_3680_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_3685_: u8 = 0;
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3685_ = 1;
    v___x_3686_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__39;
    v___x_3687_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3686_, v___x_3685_);
    return v___x_3687_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__40), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__40_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__40);
    v___x_3689_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3690_ = lean_string_append(v___x_3689_, v___x_3688_);
    return v___x_3690_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3691_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3692_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__41), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__41_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__41);
    v___x_3693_ = lean_string_append(v___x_3692_, v___x_3691_);
    return v___x_3693_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_3697_: u8 = 0;
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = 1;
    v___x_3698_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__44;
    v___x_3699_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3698_, v___x_3697_);
    return v___x_3699_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__45), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__45_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__45);
    v___x_3701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3702_ = lean_string_append(v___x_3701_, v___x_3700_);
    return v___x_3702_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3703_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3704_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__46), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__46_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__46);
    v___x_3705_ = lean_string_append(v___x_3704_, v___x_3703_);
    return v___x_3705_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3710_ = 1;
    v___x_3711_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__50;
    v___x_3712_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3711_, v___x_3710_);
    return v___x_3712_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__52()
-> *mut leanh::LeanObject {
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3713_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__51), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__51_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__51);
    v___x_3714_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3715_ = lean_string_append(v___x_3714_, v___x_3713_);
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3717_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__52), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__52_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__52);
    v___x_3718_ = lean_string_append(v___x_3717_, v___x_3716_);
    return v___x_3718_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__57()
-> *mut leanh::LeanObject {
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = 1;
    v___x_3724_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__56;
    v___x_3725_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3724_, v___x_3723_);
    return v___x_3725_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3726_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__57), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__57_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__57);
    v___x_3727_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3728_ = lean_string_append(v___x_3727_, v___x_3726_);
    return v___x_3728_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3730_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__58), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__58_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__58);
    v___x_3731_ = lean_string_append(v___x_3730_, v___x_3729_);
    return v___x_3731_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__63()
-> *mut leanh::LeanObject {
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3736_ = 1;
    v___x_3737_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__62;
    v___x_3738_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3737_, v___x_3736_);
    return v___x_3738_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__64()
-> *mut leanh::LeanObject {
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3739_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__63), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__63_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__63);
    v___x_3740_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__7);
    v___x_3741_ = lean_string_append(v___x_3740_, v___x_3739_);
    return v___x_3741_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__65()
-> *mut leanh::LeanObject {
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3742_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_3743_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__64), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__64_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__64);
    v___x_3744_ = lean_string_append(v___x_3743_, v___x_3742_);
    return v___x_3744_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1(
    mut v_json_3746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3758_: u8 = 0;
    let mut v_a_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_a_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_a_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_a_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3800_: u8 = 0;
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut v_a_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3815_: u8 = 0;
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut v_a_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_a_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_a_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_a_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v_a_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3871_: u8 = 0;
    let mut v_a_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_a_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut v_a_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_a_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_a_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3930_: u8 = 0;
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut v_a_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3941_: u8 = 0;
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut v_a_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3955_: u8 = 0;
    let mut v_a_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3747_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0;
                leanh::lean_inc(v_json_3746_);
                v___x_3748_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__5(v_json_3746_, v___x_3747_);
                if leanh::lean_obj_tag(v___x_3748_) == 0 {
                    leanh::lean_dec(v_json_3746_);
                    v_a_3749_ = leanh::lean_ctor_get(v___x_3748_, 0);
                    v_isSharedCheck_3758_ = (!leanh::lean_is_exclusive(v___x_3748_)) as u8;
                    if v_isSharedCheck_3758_ == 0 {
                        v___x_3751_ = v___x_3748_;
                        v_isShared_3752_ = v_isSharedCheck_3758_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3749_);
                        leanh::lean_dec(v___x_3748_);
                        v___x_3751_ = leanh::lean_box(0);
                        v_isShared_3752_ = v_isSharedCheck_3758_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_3748_) == 0 {
                        leanh::lean_dec(v_json_3746_);
                        v_a_3759_ = leanh::lean_ctor_get(v___x_3748_, 0);
                        v_isSharedCheck_3766_ =
                            (!leanh::lean_is_exclusive(v___x_3748_)) as u8;
                        if v_isSharedCheck_3766_ == 0 {
                            v___x_3761_ = v___x_3748_;
                            v_isShared_3762_ = v_isSharedCheck_3766_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3759_);
                            leanh::lean_dec(v___x_3748_);
                            v___x_3761_ = leanh::lean_box(0);
                            v_isShared_3762_ = v_isSharedCheck_3766_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3767_ = leanh::lean_ctor_get(v___x_3748_, 0);
                        leanh::lean_inc(v_a_3767_);
                        leanh::lean_dec_ref_known(v___x_3748_, 1);
                        v___x_3768_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__13;
                        leanh::lean_inc(v_json_3746_);
                        v___x_3769_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__6(v_json_3746_, v___x_3768_);
                        if leanh::lean_obj_tag(v___x_3769_) == 0 {
                            leanh::lean_dec(v_a_3767_);
                            leanh::lean_dec(v_json_3746_);
                            v_a_3770_ = leanh::lean_ctor_get(v___x_3769_, 0);
                            v_isSharedCheck_3779_ =
                                (!leanh::lean_is_exclusive(v___x_3769_)) as u8;
                            if v_isSharedCheck_3779_ == 0 {
                                v___x_3772_ = v___x_3769_;
                                v_isShared_3773_ = v_isSharedCheck_3779_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3770_);
                                leanh::lean_dec(v___x_3769_);
                                v___x_3772_ = leanh::lean_box(0);
                                v_isShared_3773_ = v_isSharedCheck_3779_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3769_) == 0 {
                                leanh::lean_dec(v_a_3767_);
                                leanh::lean_dec(v_json_3746_);
                                v_a_3780_ = leanh::lean_ctor_get(v___x_3769_, 0);
                                v_isSharedCheck_3787_ =
                                    (!leanh::lean_is_exclusive(v___x_3769_)) as u8;
                                if v_isSharedCheck_3787_ == 0 {
                                    v___x_3782_ = v___x_3769_;
                                    v_isShared_3783_ = v_isSharedCheck_3787_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3780_);
                                    leanh::lean_dec(v___x_3769_);
                                    v___x_3782_ = leanh::lean_box(0);
                                    v_isShared_3783_ = v_isSharedCheck_3787_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3788_ = leanh::lean_ctor_get(v___x_3769_, 0);
                                leanh::lean_inc(v_a_3788_);
                                leanh::lean_dec_ref_known(v___x_3769_, 1);
                                v___x_3789_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__19;
                                leanh::lean_inc(v_json_3746_);
                                v___x_3790_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__7(v_json_3746_, v___x_3789_);
                                if leanh::lean_obj_tag(v___x_3790_) == 0 {
                                    leanh::lean_dec(v_a_3788_);
                                    leanh::lean_dec(v_a_3767_);
                                    leanh::lean_dec(v_json_3746_);
                                    v_a_3791_ = leanh::lean_ctor_get(v___x_3790_, 0);
                                    v_isSharedCheck_3800_ =
                                        (!leanh::lean_is_exclusive(v___x_3790_)) as u8;
                                    if v_isSharedCheck_3800_ == 0 {
                                        v___x_3793_ = v___x_3790_;
                                        v_isShared_3794_ = v_isSharedCheck_3800_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3791_);
                                        leanh::lean_dec(v___x_3790_);
                                        v___x_3793_ = leanh::lean_box(0);
                                        v_isShared_3794_ = v_isSharedCheck_3800_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_3790_) == 0 {
                                        leanh::lean_dec(v_a_3788_);
                                        leanh::lean_dec(v_a_3767_);
                                        leanh::lean_dec(v_json_3746_);
                                        v_a_3801_ = leanh::lean_ctor_get(v___x_3790_, 0);
                                        v_isSharedCheck_3808_ =
                                            (!leanh::lean_is_exclusive(v___x_3790_)) as u8;
                                        if v_isSharedCheck_3808_ == 0 {
                                            v___x_3803_ = v___x_3790_;
                                            v_isShared_3804_ = v_isSharedCheck_3808_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3801_);
                                            leanh::lean_dec(v___x_3790_);
                                            v___x_3803_ = leanh::lean_box(0);
                                            v_isShared_3804_ = v_isSharedCheck_3808_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_3809_ = leanh::lean_ctor_get(v___x_3790_, 0);
                                        leanh::lean_inc(v_a_3809_);
                                        leanh::lean_dec_ref_known(v___x_3790_, 1);
                                        v___x_3810_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__25;
                                        leanh::lean_inc(v_json_3746_);
                                        v___x_3811_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_3746_, v___x_3810_);
                                        if leanh::lean_obj_tag(v___x_3811_) == 0 {
                                            leanh::lean_dec(v_a_3809_);
                                            leanh::lean_dec(v_a_3788_);
                                            leanh::lean_dec(v_a_3767_);
                                            leanh::lean_dec(v_json_3746_);
                                            v_a_3812_ = leanh::lean_ctor_get(v___x_3811_, 0);
                                            v_isSharedCheck_3821_ =
                                                (!leanh::lean_is_exclusive(v___x_3811_))
                                                    as u8;
                                            if v_isSharedCheck_3821_ == 0 {
                                                v___x_3814_ = v___x_3811_;
                                                v_isShared_3815_ = v_isSharedCheck_3821_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3812_);
                                                leanh::lean_dec(v___x_3811_);
                                                v___x_3814_ = leanh::lean_box(0);
                                                v_isShared_3815_ = v_isSharedCheck_3821_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_3811_) == 0 {
                                                leanh::lean_dec(v_a_3809_);
                                                leanh::lean_dec(v_a_3788_);
                                                leanh::lean_dec(v_a_3767_);
                                                leanh::lean_dec(v_json_3746_);
                                                v_a_3822_ =
                                                    leanh::lean_ctor_get(v___x_3811_, 0);
                                                v_isSharedCheck_3829_ =
                                                    (!leanh::lean_is_exclusive(v___x_3811_))
                                                        as u8;
                                                if v_isSharedCheck_3829_ == 0 {
                                                    v___x_3824_ = v___x_3811_;
                                                    v_isShared_3825_ = v_isSharedCheck_3829_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3822_);
                                                    leanh::lean_dec(v___x_3811_);
                                                    v___x_3824_ = leanh::lean_box(0);
                                                    v_isShared_3825_ = v_isSharedCheck_3829_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_3830_ =
                                                    leanh::lean_ctor_get(v___x_3811_, 0);
                                                leanh::lean_inc(v_a_3830_);
                                                leanh::lean_dec_ref_known(v___x_3811_, 1);
                                                v___x_3831_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__31;
                                                leanh::lean_inc(v_json_3746_);
                                                v___x_3832_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__9(v_json_3746_, v___x_3831_);
                                                if leanh::lean_obj_tag(v___x_3832_) == 0 {
                                                    leanh::lean_dec(v_a_3830_);
                                                    leanh::lean_dec(v_a_3809_);
                                                    leanh::lean_dec(v_a_3788_);
                                                    leanh::lean_dec(v_a_3767_);
                                                    leanh::lean_dec(v_json_3746_);
                                                    v_a_3833_ =
                                                        leanh::lean_ctor_get(v___x_3832_, 0);
                                                    v_isSharedCheck_3842_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3832_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3842_ == 0 {
                                                        v___x_3835_ = v___x_3832_;
                                                        v_isShared_3836_ = v_isSharedCheck_3842_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3833_);
                                                        leanh::lean_dec(v___x_3832_);
                                                        v___x_3835_ = leanh::lean_box(0);
                                                        v_isShared_3836_ = v_isSharedCheck_3842_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_3832_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_3830_);
                                                        leanh::lean_dec(v_a_3809_);
                                                        leanh::lean_dec(v_a_3788_);
                                                        leanh::lean_dec(v_a_3767_);
                                                        leanh::lean_dec(v_json_3746_);
                                                        v_a_3843_ = leanh::lean_ctor_get(
                                                            v___x_3832_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3850_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3832_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3850_ == 0 {
                                                            v___x_3845_ = v___x_3832_;
                                                            v_isShared_3846_ =
                                                                v_isSharedCheck_3850_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3843_);
                                                            leanh::lean_dec(v___x_3832_);
                                                            v___x_3845_ = leanh::lean_box(0);
                                                            v_isShared_3846_ =
                                                                v_isSharedCheck_3850_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_3851_ = leanh::lean_ctor_get(
                                                            v___x_3832_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_3851_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_3832_,
                                                            1,
                                                        );
                                                        v___x_3852_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__37;
                                                        leanh::lean_inc(v_json_3746_);
                                                        v___x_3853_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_json_3746_, v___x_3852_);
                                                        if leanh::lean_obj_tag(v___x_3853_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_3851_);
                                                            leanh::lean_dec(v_a_3830_);
                                                            leanh::lean_dec(v_a_3809_);
                                                            leanh::lean_dec(v_a_3788_);
                                                            leanh::lean_dec(v_a_3767_);
                                                            leanh::lean_dec(v_json_3746_);
                                                            v_a_3854_ = leanh::lean_ctor_get(
                                                                v___x_3853_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3863_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_3853_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3863_ == 0 {
                                                                v___x_3856_ = v___x_3853_;
                                                                v_isShared_3857_ =
                                                                    v_isSharedCheck_3863_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_3854_);
                                                                leanh::lean_dec(v___x_3853_);
                                                                v___x_3856_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_3857_ =
                                                                    v_isSharedCheck_3863_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v___x_3853_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec(v_a_3851_);
                                                                leanh::lean_dec(v_a_3830_);
                                                                leanh::lean_dec(v_a_3809_);
                                                                leanh::lean_dec(v_a_3788_);
                                                                leanh::lean_dec(v_a_3767_);
                                                                leanh::lean_dec(
                                                                    v_json_3746_,
                                                                );
                                                                v_a_3864_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3853_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3871_ = (!leanh::lean_is_exclusive(v___x_3853_)) as u8;
                                                                if v_isSharedCheck_3871_ == 0 {
                                                                    v___x_3866_ = v___x_3853_;
                                                                    v_isShared_3867_ =
                                                                        v_isSharedCheck_3871_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_3864_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3853_,
                                                                    );
                                                                    v___x_3866_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3867_ =
                                                                        v_isSharedCheck_3871_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_3872_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3853_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_3872_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_3853_,
                                                                    1,
                                                                );
                                                                v___x_3873_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__43;
                                                                leanh::lean_inc(
                                                                    v_json_3746_,
                                                                );
                                                                v___x_3874_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__11(v_json_3746_, v___x_3873_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_3874_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec(
                                                                        v_a_3872_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3851_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3830_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3809_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3788_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3767_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_json_3746_,
                                                                    );
                                                                    v_a_3875_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3874_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3884_ = (!leanh::lean_is_exclusive(v___x_3874_)) as u8;
                                                                    if v_isSharedCheck_3884_ == 0 {
                                                                        v___x_3877_ = v___x_3874_;
                                                                        v_isShared_3878_ =
                                                                            v_isSharedCheck_3884_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_3875_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3874_,
                                                                        );
                                                                        v___x_3877_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3878_ =
                                                                            v_isSharedCheck_3884_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_3874_,
                                                                    ) == 0
                                                                    {
                                                                        leanh::lean_dec(
                                                                            v_a_3872_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3851_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3830_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3809_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3788_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3767_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_json_3746_,
                                                                        );
                                                                        v_a_3885_ = leanh::lean_ctor_get(v___x_3874_, 0);
                                                                        v_isSharedCheck_3892_ = (!leanh::lean_is_exclusive(v___x_3874_)) as u8;
                                                                        if v_isSharedCheck_3892_
                                                                            == 0
                                                                        {
                                                                            v___x_3887_ =
                                                                                v___x_3874_;
                                                                            v_isShared_3888_ = v_isSharedCheck_3892_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_3885_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3874_,
                                                                            );
                                                                            v___x_3887_ = leanh::lean_box(0);
                                                                            v_isShared_3888_ = v_isSharedCheck_3892_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_3893_ = leanh::lean_ctor_get(v___x_3874_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_3893_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_3874_, 1);
                                                                        v___x_3894_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__48;
                                                                        leanh::lean_inc(
                                                                            v_json_3746_,
                                                                        );
                                                                        v___x_3895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__12(v_json_3746_, v___x_3894_);
                                                                        if leanh::lean_obj_tag(v___x_3895_) == 0 {
leanh::lean_dec(v_a_3893_);
leanh::lean_dec(v_a_3872_);
leanh::lean_dec(v_a_3851_);
leanh::lean_dec(v_a_3830_);
leanh::lean_dec(v_a_3809_);
leanh::lean_dec(v_a_3788_);
leanh::lean_dec(v_a_3767_);
leanh::lean_dec(v_json_3746_);
v_a_3896_ = leanh::lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3905_ = (!leanh::lean_is_exclusive(v___x_3895_)) as u8;
if v_isSharedCheck_3905_ == 0 {
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3905_;
state = 29; continue;
} else {
leanh::lean_inc(v_a_3896_);
leanh::lean_dec(v___x_3895_);
v___x_3898_ = leanh::lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3905_;
state = 29; continue;
}
} else {
if leanh::lean_obj_tag(v___x_3895_) == 0 {
leanh::lean_dec(v_a_3893_);
leanh::lean_dec(v_a_3872_);
leanh::lean_dec(v_a_3851_);
leanh::lean_dec(v_a_3830_);
leanh::lean_dec(v_a_3809_);
leanh::lean_dec(v_a_3788_);
leanh::lean_dec(v_a_3767_);
leanh::lean_dec(v_json_3746_);
v_a_3906_ = leanh::lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3913_ = (!leanh::lean_is_exclusive(v___x_3895_)) as u8;
if v_isSharedCheck_3913_ == 0 {
v___x_3908_ = v___x_3895_;
v_isShared_3909_ = v_isSharedCheck_3913_;
state = 31; continue;
} else {
leanh::lean_inc(v_a_3906_);
leanh::lean_dec(v___x_3895_);
v___x_3908_ = leanh::lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
state = 31; continue;
}
} else {
v_a_3914_ = leanh::lean_ctor_get(v___x_3895_, 0);
leanh::lean_inc(v_a_3914_);
leanh::lean_dec_ref_known(v___x_3895_, 1);
v___x_3915_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__54;
leanh::lean_inc(v_json_3746_);
v___x_3916_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__13(v_json_3746_, v___x_3915_);
if leanh::lean_obj_tag(v___x_3916_) == 0 {
leanh::lean_dec(v_a_3914_);
leanh::lean_dec(v_a_3893_);
leanh::lean_dec(v_a_3872_);
leanh::lean_dec(v_a_3851_);
leanh::lean_dec(v_a_3830_);
leanh::lean_dec(v_a_3809_);
leanh::lean_dec(v_a_3788_);
leanh::lean_dec(v_a_3767_);
leanh::lean_dec(v_json_3746_);
v_a_3917_ = leanh::lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3926_ = (!leanh::lean_is_exclusive(v___x_3916_)) as u8;
if v_isSharedCheck_3926_ == 0 {
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3926_;
state = 33; continue;
} else {
leanh::lean_inc(v_a_3917_);
leanh::lean_dec(v___x_3916_);
v___x_3919_ = leanh::lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3926_;
state = 33; continue;
}
} else {
if leanh::lean_obj_tag(v___x_3916_) == 0 {
leanh::lean_dec(v_a_3914_);
leanh::lean_dec(v_a_3893_);
leanh::lean_dec(v_a_3872_);
leanh::lean_dec(v_a_3851_);
leanh::lean_dec(v_a_3830_);
leanh::lean_dec(v_a_3809_);
leanh::lean_dec(v_a_3788_);
leanh::lean_dec(v_a_3767_);
leanh::lean_dec(v_json_3746_);
v_a_3927_ = leanh::lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3934_ = (!leanh::lean_is_exclusive(v___x_3916_)) as u8;
if v_isSharedCheck_3934_ == 0 {
v___x_3929_ = v___x_3916_;
v_isShared_3930_ = v_isSharedCheck_3934_;
state = 35; continue;
} else {
leanh::lean_inc(v_a_3927_);
leanh::lean_dec(v___x_3916_);
v___x_3929_ = leanh::lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
state = 35; continue;
}
} else {
v_a_3935_ = leanh::lean_ctor_get(v___x_3916_, 0);
leanh::lean_inc(v_a_3935_);
leanh::lean_dec_ref_known(v___x_3916_, 1);
v___x_3936_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__60;
leanh::lean_inc(v_json_3746_);
v___x_3937_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__14(v_json_3746_, v___x_3936_);
if leanh::lean_obj_tag(v___x_3937_) == 0 {
leanh::lean_dec(v_a_3935_);
leanh::lean_dec(v_a_3914_);
leanh::lean_dec(v_a_3893_);
leanh::lean_dec(v_a_3872_);
leanh::lean_dec(v_a_3851_);
leanh::lean_dec(v_a_3830_);
leanh::lean_dec(v_a_3809_);
leanh::lean_dec(v_a_3788_);
leanh::lean_dec(v_a_3767_);
leanh::lean_dec(v_json_3746_);
v_a_3938_ = leanh::lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3947_ = (!leanh::lean_is_exclusive(v___x_3937_)) as u8;
if v_isSharedCheck_3947_ == 0 {
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3947_;
state = 37; continue;
} else {
leanh::lean_inc(v_a_3938_);
leanh::lean_dec(v___x_3937_);
v___x_3940_ = leanh::lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3947_;
state = 37; continue;
}
} else {
if leanh::lean_obj_tag(v___x_3937_) == 0 {
leanh::lean_dec(v_a_3935_);
leanh::lean_dec(v_a_3914_);
leanh::lean_dec(v_a_3893_);
leanh::lean_dec(v_a_3872_);
leanh::lean_dec(v_a_3851_);
leanh::lean_dec(v_a_3830_);
leanh::lean_dec(v_a_3809_);
leanh::lean_dec(v_a_3788_);
leanh::lean_dec(v_a_3767_);
leanh::lean_dec(v_json_3746_);
v_a_3948_ = leanh::lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3955_ = (!leanh::lean_is_exclusive(v___x_3937_)) as u8;
if v_isSharedCheck_3955_ == 0 {
v___x_3950_ = v___x_3937_;
v_isShared_3951_ = v_isSharedCheck_3955_;
state = 39; continue;
} else {
leanh::lean_inc(v_a_3948_);
leanh::lean_dec(v___x_3937_);
v___x_3950_ = leanh::lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
state = 39; continue;
}
} else {
v_a_3956_ = leanh::lean_ctor_get(v___x_3937_, 0);
leanh::lean_inc(v_a_3956_);
leanh::lean_dec_ref_known(v___x_3937_, 1);
v___x_3957_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66;
v___x_3958_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15(v_json_3746_, v___x_3957_);
v_a_3959_ = leanh::lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3967_ = (!leanh::lean_is_exclusive(v___x_3958_)) as u8;
if v_isSharedCheck_3967_ == 0 {
v___x_3961_ = v___x_3958_;
v_isShared_3962_ = v_isSharedCheck_3967_;
state = 41; continue;
} else {
leanh::lean_inc(v_a_3959_);
leanh::lean_dec(v___x_3958_);
v___x_3961_ = leanh::lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3967_;
state = 41; continue;
}
}
}
}
}
}
}
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3753_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__12), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__12_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__12);
                v___x_3754_ = lean_string_append(v___x_3753_, v_a_3749_);
                leanh::lean_dec(v_a_3749_);
                if v_isShared_3752_ == 0 {
                    leanh::lean_ctor_set(v___x_3751_, 0, v___x_3754_);
                    v___x_3756_ = v___x_3751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
                    v___x_3756_ = v_reuseFailAlloc_3757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3756_;
            }
            3 => {
                if v_isShared_3762_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3761_, 0);
                    v___x_3764_ = v___x_3761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
                    v___x_3764_ = v_reuseFailAlloc_3765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3764_;
            }
            5 => {
                v___x_3774_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__18), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__18_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__18);
                v___x_3775_ = lean_string_append(v___x_3774_, v_a_3770_);
                leanh::lean_dec(v_a_3770_);
                if v_isShared_3773_ == 0 {
                    leanh::lean_ctor_set(v___x_3772_, 0, v___x_3775_);
                    v___x_3777_ = v___x_3772_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
                    v___x_3777_ = v_reuseFailAlloc_3778_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3777_;
            }
            7 => {
                if v_isShared_3783_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3782_, 0);
                    v___x_3785_ = v___x_3782_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
                    v___x_3785_ = v_reuseFailAlloc_3786_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3785_;
            }
            9 => {
                v___x_3795_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__24_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__24);
                v___x_3796_ = lean_string_append(v___x_3795_, v_a_3791_);
                leanh::lean_dec(v_a_3791_);
                if v_isShared_3794_ == 0 {
                    leanh::lean_ctor_set(v___x_3793_, 0, v___x_3796_);
                    v___x_3798_ = v___x_3793_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
                    v___x_3798_ = v_reuseFailAlloc_3799_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3798_;
            }
            11 => {
                if v_isShared_3804_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3803_, 0);
                    v___x_3806_ = v___x_3803_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3806_;
            }
            13 => {
                v___x_3816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__30), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__30_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__30);
                v___x_3817_ = lean_string_append(v___x_3816_, v_a_3812_);
                leanh::lean_dec(v_a_3812_);
                if v_isShared_3815_ == 0 {
                    leanh::lean_ctor_set(v___x_3814_, 0, v___x_3817_);
                    v___x_3819_ = v___x_3814_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
                    v___x_3819_ = v_reuseFailAlloc_3820_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3819_;
            }
            15 => {
                if v_isShared_3825_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3824_, 0);
                    v___x_3827_ = v___x_3824_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
                    v___x_3827_ = v_reuseFailAlloc_3828_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3827_;
            }
            17 => {
                v___x_3837_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__36), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__36_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__36);
                v___x_3838_ = lean_string_append(v___x_3837_, v_a_3833_);
                leanh::lean_dec(v_a_3833_);
                if v_isShared_3836_ == 0 {
                    leanh::lean_ctor_set(v___x_3835_, 0, v___x_3838_);
                    v___x_3840_ = v___x_3835_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
                    v___x_3840_ = v_reuseFailAlloc_3841_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3840_;
            }
            19 => {
                if v_isShared_3846_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3845_, 0);
                    v___x_3848_ = v___x_3845_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
                    v___x_3848_ = v_reuseFailAlloc_3849_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3848_;
            }
            21 => {
                v___x_3858_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__42), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__42_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__42);
                v___x_3859_ = lean_string_append(v___x_3858_, v_a_3854_);
                leanh::lean_dec(v_a_3854_);
                if v_isShared_3857_ == 0 {
                    leanh::lean_ctor_set(v___x_3856_, 0, v___x_3859_);
                    v___x_3861_ = v___x_3856_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
                    v___x_3861_ = v_reuseFailAlloc_3862_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3861_;
            }
            23 => {
                if v_isShared_3867_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3866_, 0);
                    v___x_3869_ = v___x_3866_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
                    v___x_3869_ = v_reuseFailAlloc_3870_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3869_;
            }
            25 => {
                v___x_3879_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__47), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__47_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__47);
                v___x_3880_ = lean_string_append(v___x_3879_, v_a_3875_);
                leanh::lean_dec(v_a_3875_);
                if v_isShared_3878_ == 0 {
                    leanh::lean_ctor_set(v___x_3877_, 0, v___x_3880_);
                    v___x_3882_ = v___x_3877_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
                    v___x_3882_ = v_reuseFailAlloc_3883_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3882_;
            }
            27 => {
                if v_isShared_3888_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3887_, 0);
                    v___x_3890_ = v___x_3887_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
                    v___x_3890_ = v_reuseFailAlloc_3891_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3890_;
            }
            29 => {
                v___x_3900_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__53), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__53_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__53);
                v___x_3901_ = lean_string_append(v___x_3900_, v_a_3896_);
                leanh::lean_dec(v_a_3896_);
                if v_isShared_3899_ == 0 {
                    leanh::lean_ctor_set(v___x_3898_, 0, v___x_3901_);
                    v___x_3903_ = v___x_3898_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3903_;
            }
            31 => {
                if v_isShared_3909_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3908_, 0);
                    v___x_3911_ = v___x_3908_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3911_;
            }
            33 => {
                v___x_3921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__59), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__59_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__59);
                v___x_3922_ = lean_string_append(v___x_3921_, v_a_3917_);
                leanh::lean_dec(v_a_3917_);
                if v_isShared_3920_ == 0 {
                    leanh::lean_ctor_set(v___x_3919_, 0, v___x_3922_);
                    v___x_3924_ = v___x_3919_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3924_;
            }
            35 => {
                if v_isShared_3930_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3929_, 0);
                    v___x_3932_ = v___x_3929_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3932_;
            }
            37 => {
                v___x_3942_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__65), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__65_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__65);
                v___x_3943_ = lean_string_append(v___x_3942_, v_a_3938_);
                leanh::lean_dec(v_a_3938_);
                if v_isShared_3941_ == 0 {
                    leanh::lean_ctor_set(v___x_3940_, 0, v___x_3943_);
                    v___x_3945_ = v___x_3940_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3946_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
                    v___x_3945_ = v_reuseFailAlloc_3946_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3945_;
            }
            39 => {
                if v_isShared_3951_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3950_, 0);
                    v___x_3953_ = v___x_3950_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3954_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
                    v___x_3953_ = v_reuseFailAlloc_3954_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3953_;
            }
            41 => {
                v___x_3963_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                leanh::lean_ctor_set(v___x_3963_, 0, v_a_3767_);
                leanh::lean_ctor_set(v___x_3963_, 1, v_a_3788_);
                leanh::lean_ctor_set(v___x_3963_, 2, v_a_3809_);
                leanh::lean_ctor_set(v___x_3963_, 3, v_a_3830_);
                leanh::lean_ctor_set(v___x_3963_, 4, v_a_3851_);
                leanh::lean_ctor_set(v___x_3963_, 5, v_a_3872_);
                leanh::lean_ctor_set(v___x_3963_, 6, v_a_3893_);
                leanh::lean_ctor_set(v___x_3963_, 7, v_a_3914_);
                leanh::lean_ctor_set(v___x_3963_, 8, v_a_3935_);
                leanh::lean_ctor_set(v___x_3963_, 9, v_a_3956_);
                leanh::lean_ctor_set(v___x_3963_, 10, v_a_3959_);
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3963_);
                    v___x_3965_ = v___x_3961_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
                    v___x_3965_ = v_reuseFailAlloc_3966_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__2(
    mut v_sz_3968_: usize,
    mut v_i_3969_: usize,
    mut v_bs_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3971_: u8 = 0;
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3978_: u8 = 0;
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3982_: u8 = 0;
    let mut v_a_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: usize = 0;
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3971_ = lean_usize_dec_lt(v_i_3969_, v_sz_3968_);
                if v___x_3971_ == 0 {
                    v___x_3972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3972_, 0, v_bs_3970_);
                    return v___x_3972_;
                } else {
                    v_v_3973_ = lean_array_uget_borrowed(v_bs_3970_, v_i_3969_);
                    leanh::lean_inc(v_v_3973_);
                    v___x_3974_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1(v_v_3973_);
                    if leanh::lean_obj_tag(v___x_3974_) == 0 {
                        leanh::lean_dec_ref(v_bs_3970_);
                        v_a_3975_ = leanh::lean_ctor_get(v___x_3974_, 0);
                        v_isSharedCheck_3982_ =
                            (!leanh::lean_is_exclusive(v___x_3974_)) as u8;
                        if v_isSharedCheck_3982_ == 0 {
                            v___x_3977_ = v___x_3974_;
                            v_isShared_3978_ = v_isSharedCheck_3982_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3975_);
                            leanh::lean_dec(v___x_3974_);
                            v___x_3977_ = leanh::lean_box(0);
                            v_isShared_3978_ = v_isSharedCheck_3982_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3983_ = leanh::lean_ctor_get(v___x_3974_, 0);
                        leanh::lean_inc(v_a_3983_);
                        leanh::lean_dec_ref_known(v___x_3974_, 1);
                        v___x_3984_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3985_ = lean_array_uset(v_bs_3970_, v_i_3969_, v___x_3984_);
                        v___x_3986_ = 1usize;
                        v___x_3987_ = lean_usize_add(v_i_3969_, v___x_3986_);
                        v___x_3988_ = lean_array_uset(v_bs_x27_3985_, v_i_3969_, v_a_3983_);
                        v_i_3969_ = v___x_3987_;
                        v_bs_3970_ = v___x_3988_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3978_ == 0 {
                    v___x_3980_ = v___x_3977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
                    v___x_3980_ = v_reuseFailAlloc_3981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__2___boxed(
    mut v_sz_3990_: *mut leanh::LeanObject,
    mut v_i_3991_: *mut leanh::LeanObject,
    mut v_bs_3992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3993_: usize = 0;
    let mut v_i_boxed_3994_: usize = 0;
    let mut v_res_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3993_ = leanh::lean_unbox_usize(v_sz_3990_);
    leanh::lean_dec(v_sz_3990_);
    v_i_boxed_3994_ = leanh::lean_unbox_usize(v_i_3991_);
    leanh::lean_dec(v_i_3991_);
    v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_3993_, v_i_boxed_3994_, v_bs_3992_);
    return v_res_3995_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0(
    mut v_x_3996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3996_) == 4 {
        let mut v_elems_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3998_: usize = 0;
        let mut v___x_3999_: usize = 0;
        let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_3997_ = leanh::lean_ctor_get(v_x_3996_, 0);
        leanh::lean_inc_ref(v_elems_3997_);
        leanh::lean_dec_ref_known(v_x_3996_, 1);
        v_sz_3998_ = lean_array_size(v_elems_3997_);
        v___x_3999_ = 0usize;
        v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__2(v_sz_3998_, v___x_3999_, v_elems_3997_);
        return v___x_4000_;
    } else {
        let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4001_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__0;
        v___x_4002_ = leanh::lean_unsigned_to_nat(80);
        v___x_4003_ = l_Lean_Json_pretty(v_x_3996_, v___x_4002_);
        v___x_4004_ = lean_string_append(v___x_4001_, v___x_4003_);
        leanh::lean_dec_ref(v___x_4003_);
        v___x_4005_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5___closed__1;
        v___x_4006_ = lean_string_append(v___x_4004_, v___x_4005_);
        v___x_4007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4007_, 0, v___x_4006_);
        return v___x_4007_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0(
    mut v_j_4008_: *mut leanh::LeanObject,
    mut v_k_4009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4010_ = l_Lean_Json_getObjValD(v_j_4008_, v_k_4009_);
    v___x_4011_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0(v___x_4010_);
    return v___x_4011_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0___boxed(
    mut v_j_4012_: *mut leanh::LeanObject,
    mut v_k_4013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4014_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0(v_j_4012_, v_k_4013_);
    leanh::lean_dec_ref(v_k_4013_);
    return v_res_4014_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = 1;
    v___x_4022_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__2;
    v___x_4023_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4022_, v___x_4021_);
    return v___x_4023_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4024_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_4025_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__3,
    );
    v___x_4026_ = lean_string_append(v___x_4025_, v___x_4024_);
    return v___x_4026_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4029_ = 1;
    v___x_4030_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__5;
    v___x_4031_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4030_, v___x_4029_);
    return v___x_4031_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4032_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__6,
    );
    v___x_4033_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4,
    );
    v___x_4034_ = lean_string_append(v___x_4033_, v___x_4032_);
    return v___x_4034_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__7,
    );
    v___x_4037_ = lean_string_append(v___x_4036_, v___x_4035_);
    return v___x_4037_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4042_: u8 = 0;
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = 1;
    v___x_4043_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__11;
    v___x_4044_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4043_, v___x_4042_);
    return v___x_4044_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__12,
    );
    v___x_4046_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4,
    );
    v___x_4047_ = lean_string_append(v___x_4046_, v___x_4045_);
    return v___x_4047_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4049_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__13,
    );
    v___x_4050_ = lean_string_append(v___x_4049_, v___x_4048_);
    return v___x_4050_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ = 1;
    v___x_4056_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__17;
    v___x_4057_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4056_, v___x_4055_);
    return v___x_4057_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4058_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__18),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__18_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__18,
    );
    v___x_4059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__4,
    );
    v___x_4060_ = lean_string_append(v___x_4059_, v___x_4058_);
    return v___x_4060_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4061_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4062_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__19_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__19,
    );
    v___x_4063_ = lean_string_append(v___x_4062_, v___x_4061_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionContext_fromJson(
    mut v_json_4064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4070_: u8 = 0;
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_a_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v_a_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_a_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut v_a_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4118_: u8 = 0;
    let mut v_a_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4126_: u8 = 0;
    let mut v_a_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4130_: u8 = 0;
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4065_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0;
                leanh::lean_inc(v_json_4064_);
                v___x_4066_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0(v_json_4064_, v___x_4065_);
                if leanh::lean_obj_tag(v___x_4066_) == 0 {
                    leanh::lean_dec(v_json_4064_);
                    v_a_4067_ = leanh::lean_ctor_get(v___x_4066_, 0);
                    v_isSharedCheck_4076_ = (!leanh::lean_is_exclusive(v___x_4066_)) as u8;
                    if v_isSharedCheck_4076_ == 0 {
                        v___x_4069_ = v___x_4066_;
                        v_isShared_4070_ = v_isSharedCheck_4076_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4067_);
                        leanh::lean_dec(v___x_4066_);
                        v___x_4069_ = leanh::lean_box(0);
                        v_isShared_4070_ = v_isSharedCheck_4076_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_4066_) == 0 {
                        leanh::lean_dec(v_json_4064_);
                        v_a_4077_ = leanh::lean_ctor_get(v___x_4066_, 0);
                        v_isSharedCheck_4084_ =
                            (!leanh::lean_is_exclusive(v___x_4066_)) as u8;
                        if v_isSharedCheck_4084_ == 0 {
                            v___x_4079_ = v___x_4066_;
                            v_isShared_4080_ = v_isSharedCheck_4084_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4077_);
                            leanh::lean_dec(v___x_4066_);
                            v___x_4079_ = leanh::lean_box(0);
                            v_isShared_4080_ = v_isSharedCheck_4084_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4085_ = leanh::lean_ctor_get(v___x_4066_, 0);
                        leanh::lean_inc(v_a_4085_);
                        leanh::lean_dec_ref_known(v___x_4066_, 1);
                        v___x_4086_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__9;
                        leanh::lean_inc(v_json_4064_);
                        v___x_4087_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1(v_json_4064_, v___x_4086_);
                        if leanh::lean_obj_tag(v___x_4087_) == 0 {
                            leanh::lean_dec(v_a_4085_);
                            leanh::lean_dec(v_json_4064_);
                            v_a_4088_ = leanh::lean_ctor_get(v___x_4087_, 0);
                            v_isSharedCheck_4097_ =
                                (!leanh::lean_is_exclusive(v___x_4087_)) as u8;
                            if v_isSharedCheck_4097_ == 0 {
                                v___x_4090_ = v___x_4087_;
                                v_isShared_4091_ = v_isSharedCheck_4097_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4088_);
                                leanh::lean_dec(v___x_4087_);
                                v___x_4090_ = leanh::lean_box(0);
                                v_isShared_4091_ = v_isSharedCheck_4097_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_4087_) == 0 {
                                leanh::lean_dec(v_a_4085_);
                                leanh::lean_dec(v_json_4064_);
                                v_a_4098_ = leanh::lean_ctor_get(v___x_4087_, 0);
                                v_isSharedCheck_4105_ =
                                    (!leanh::lean_is_exclusive(v___x_4087_)) as u8;
                                if v_isSharedCheck_4105_ == 0 {
                                    v___x_4100_ = v___x_4087_;
                                    v_isShared_4101_ = v_isSharedCheck_4105_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4098_);
                                    leanh::lean_dec(v___x_4087_);
                                    v___x_4100_ = leanh::lean_box(0);
                                    v_isShared_4101_ = v_isSharedCheck_4105_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4106_ = leanh::lean_ctor_get(v___x_4087_, 0);
                                leanh::lean_inc(v_a_4106_);
                                leanh::lean_dec_ref_known(v___x_4087_, 1);
                                v___x_4107_ =
                                    l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__15;
                                v___x_4108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__2(v_json_4064_, v___x_4107_);
                                if leanh::lean_obj_tag(v___x_4108_) == 0 {
                                    leanh::lean_dec(v_a_4106_);
                                    leanh::lean_dec(v_a_4085_);
                                    v_a_4109_ = leanh::lean_ctor_get(v___x_4108_, 0);
                                    v_isSharedCheck_4118_ =
                                        (!leanh::lean_is_exclusive(v___x_4108_)) as u8;
                                    if v_isSharedCheck_4118_ == 0 {
                                        v___x_4111_ = v___x_4108_;
                                        v_isShared_4112_ = v_isSharedCheck_4118_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4109_);
                                        leanh::lean_dec(v___x_4108_);
                                        v___x_4111_ = leanh::lean_box(0);
                                        v_isShared_4112_ = v_isSharedCheck_4118_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_4108_) == 0 {
                                        leanh::lean_dec(v_a_4106_);
                                        leanh::lean_dec(v_a_4085_);
                                        v_a_4119_ = leanh::lean_ctor_get(v___x_4108_, 0);
                                        v_isSharedCheck_4126_ =
                                            (!leanh::lean_is_exclusive(v___x_4108_)) as u8;
                                        if v_isSharedCheck_4126_ == 0 {
                                            v___x_4121_ = v___x_4108_;
                                            v_isShared_4122_ = v_isSharedCheck_4126_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4119_);
                                            leanh::lean_dec(v___x_4108_);
                                            v___x_4121_ = leanh::lean_box(0);
                                            v_isShared_4122_ = v_isSharedCheck_4126_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4127_ = leanh::lean_ctor_get(v___x_4108_, 0);
                                        v_isSharedCheck_4135_ =
                                            (!leanh::lean_is_exclusive(v___x_4108_)) as u8;
                                        if v_isSharedCheck_4135_ == 0 {
                                            v___x_4129_ = v___x_4108_;
                                            v_isShared_4130_ = v_isSharedCheck_4135_;
                                            state = 13;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4127_);
                                            leanh::lean_dec(v___x_4108_);
                                            v___x_4129_ = leanh::lean_box(0);
                                            v_isShared_4130_ = v_isSharedCheck_4135_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4071_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__8,
                );
                v___x_4072_ = lean_string_append(v___x_4071_, v_a_4067_);
                leanh::lean_dec(v_a_4067_);
                if v_isShared_4070_ == 0 {
                    leanh::lean_ctor_set(v___x_4069_, 0, v___x_4072_);
                    v___x_4074_ = v___x_4069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4075_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
                    v___x_4074_ = v_reuseFailAlloc_4075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4074_;
            }
            3 => {
                if v_isShared_4080_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4079_, 0);
                    v___x_4082_ = v___x_4079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4083_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
                    v___x_4082_ = v_reuseFailAlloc_4083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4082_;
            }
            5 => {
                v___x_4092_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__14,
                );
                v___x_4093_ = lean_string_append(v___x_4092_, v_a_4088_);
                leanh::lean_dec(v_a_4088_);
                if v_isShared_4091_ == 0 {
                    leanh::lean_ctor_set(v___x_4090_, 0, v___x_4093_);
                    v___x_4095_ = v___x_4090_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4095_;
            }
            7 => {
                if v_isShared_4101_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4100_, 0);
                    v___x_4103_ = v___x_4100_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4104_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
                    v___x_4103_ = v_reuseFailAlloc_4104_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4103_;
            }
            9 => {
                v___x_4113_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__20_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__20,
                );
                v___x_4114_ = lean_string_append(v___x_4113_, v_a_4109_);
                leanh::lean_dec(v_a_4109_);
                if v_isShared_4112_ == 0 {
                    leanh::lean_ctor_set(v___x_4111_, 0, v___x_4114_);
                    v___x_4116_ = v___x_4111_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
                    v___x_4116_ = v_reuseFailAlloc_4117_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4116_;
            }
            11 => {
                if v_isShared_4122_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4121_, 0);
                    v___x_4124_ = v___x_4121_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
                    v___x_4124_ = v_reuseFailAlloc_4125_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4124_;
            }
            13 => {
                v___x_4131_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4131_, 0, v_a_4085_);
                leanh::lean_ctor_set(v___x_4131_, 1, v_a_4106_);
                leanh::lean_ctor_set(v___x_4131_, 2, v_a_4127_);
                if v_isShared_4130_ == 0 {
                    leanh::lean_ctor_set(v___x_4129_, 0, v___x_4131_);
                    v___x_4133_ = v___x_4129_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
                    v___x_4133_ = v_reuseFailAlloc_4134_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__2(
    mut v_k_4138_: *mut leanh::LeanObject,
    mut v_x_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4139_) == 0 {
                    leanh::lean_dec_ref(v_k_4138_);
                    v___x_4145_ = leanh::lean_box(0);
                    return v___x_4145_;
                } else {
                    v_val_4146_ = leanh::lean_ctor_get(v_x_4139_, 0);
                    v___x_4147_ = (leanh::lean_unbox(v_val_4146_) as u8);
                    if v___x_4147_ == 0 {
                        v___x_4148_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1);
                        v___y_4141_ = v___x_4148_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4149_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3);
                        v___y_4141_ = v___x_4149_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_4141_);
                v___x_4142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4142_, 0, v_k_4138_);
                leanh::lean_ctor_set(v___x_4142_, 1, v___y_4141_);
                v___x_4143_ = leanh::lean_box(0);
                v___x_4144_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4144_, 0, v___x_4142_);
                leanh::lean_ctor_set(v___x_4144_, 1, v___x_4143_);
                return v___x_4144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__2___boxed(
    mut v_k_4150_: *mut leanh::LeanObject,
    mut v_x_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__2(
        v_k_4150_, v_x_4151_,
    );
    leanh::lean_dec(v_x_4151_);
    return v_res_4152_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9_spec__14_spec__20(
    mut v_sz_4153_: usize,
    mut v_i_4154_: usize,
    mut v_bs_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4156_: u8 = 0;
    let mut v_v_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: usize = 0;
    let mut v___x_4162_: usize = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4156_ = lean_usize_dec_lt(v_i_4154_, v_sz_4153_);
                if v___x_4156_ == 0 {
                    return v_bs_4155_;
                } else {
                    v_v_4157_ = lean_array_uget(v_bs_4155_, v_i_4154_);
                    v___x_4158_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4159_ = lean_array_uset(v_bs_4155_, v_i_4154_, v___x_4158_);
                    v___x_4160_ =
                        l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_v_4157_);
                    v___x_4161_ = 1usize;
                    v___x_4162_ = lean_usize_add(v_i_4154_, v___x_4161_);
                    v___x_4163_ = lean_array_uset(v_bs_x27_4159_, v_i_4154_, v___x_4160_);
                    v_i_4154_ = v___x_4162_;
                    v_bs_4155_ = v___x_4163_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9_spec__14_spec__20___boxed(
    mut v_sz_4165_: *mut leanh::LeanObject,
    mut v_i_4166_: *mut leanh::LeanObject,
    mut v_bs_4167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4168_: usize = 0;
    let mut v_i_boxed_4169_: usize = 0;
    let mut v_res_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4168_ = leanh::lean_unbox_usize(v_sz_4165_);
    leanh::lean_dec(v_sz_4165_);
    v_i_boxed_4169_ = leanh::lean_unbox_usize(v_i_4166_);
    leanh::lean_dec(v_i_4166_);
    v_res_4170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9_spec__14_spec__20(v_sz_boxed_4168_, v_i_boxed_4169_, v_bs_4167_);
    return v_res_4170_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9_spec__14(
    mut v_a_4171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4172_: usize = 0;
    let mut v___x_4173_: usize = 0;
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4172_ = lean_array_size(v_a_4171_);
    v___x_4173_ = 0usize;
    v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9_spec__14_spec__20(v_sz_4172_, v___x_4173_, v_a_4171_);
    v___x_4175_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4175_, 0, v___x_4174_);
    return v___x_4175_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9(
    mut v_k_4176_: *mut leanh::LeanObject,
    mut v_x_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4177_) == 0 {
        let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4176_);
        v___x_4178_ = leanh::lean_box(0);
        return v___x_4178_;
    } else {
        let mut v_val_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4179_ = leanh::lean_ctor_get(v_x_4177_, 0);
        leanh::lean_inc(v_val_4179_);
        leanh::lean_dec_ref_known(v_x_4177_, 1);
        v___x_4180_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9_spec__14(v_val_4179_);
        v___x_4181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4181_, 0, v_k_4176_);
        leanh::lean_ctor_set(v___x_4181_, 1, v___x_4180_);
        v___x_4182_ = leanh::lean_box(0);
        v___x_4183_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4183_, 0, v___x_4181_);
        leanh::lean_ctor_set(v___x_4183_, 1, v___x_4182_);
        return v___x_4183_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__5(
    mut v_k_4184_: *mut leanh::LeanObject,
    mut v_x_4185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4196_: u8 = 0;
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4201_: u8 = 0;
    let mut v_s_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4205_: u8 = 0;
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4185_) == 0 {
                    leanh::lean_dec_ref(v_k_4184_);
                    v___x_4191_ = leanh::lean_box(0);
                    return v___x_4191_;
                } else {
                    v_val_4192_ = leanh::lean_ctor_get(v_x_4185_, 0);
                    leanh::lean_inc(v_val_4192_);
                    leanh::lean_dec_ref_known(v_x_4185_, 1);
                    if leanh::lean_obj_tag(v_val_4192_) == 0 {
                        v_i_4193_ = leanh::lean_ctor_get(v_val_4192_, 0);
                        v_isSharedCheck_4201_ =
                            (!leanh::lean_is_exclusive(v_val_4192_)) as u8;
                        if v_isSharedCheck_4201_ == 0 {
                            v___x_4195_ = v_val_4192_;
                            v_isShared_4196_ = v_isSharedCheck_4201_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_i_4193_);
                            leanh::lean_dec(v_val_4192_);
                            v___x_4195_ = leanh::lean_box(0);
                            v_isShared_4196_ = v_isSharedCheck_4201_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_s_4202_ = leanh::lean_ctor_get(v_val_4192_, 0);
                        v_isSharedCheck_4209_ =
                            (!leanh::lean_is_exclusive(v_val_4192_)) as u8;
                        if v_isSharedCheck_4209_ == 0 {
                            v___x_4204_ = v_val_4192_;
                            v_isShared_4205_ = v_isSharedCheck_4209_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_4202_);
                            leanh::lean_dec(v_val_4192_);
                            v___x_4204_ = leanh::lean_box(0);
                            v_isShared_4205_ = v_isSharedCheck_4209_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4188_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4188_, 0, v_k_4184_);
                leanh::lean_ctor_set(v___x_4188_, 1, v___y_4187_);
                v___x_4189_ = leanh::lean_box(0);
                v___x_4190_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4190_, 0, v___x_4188_);
                leanh::lean_ctor_set(v___x_4190_, 1, v___x_4189_);
                return v___x_4190_;
            }
            2 => {
                v___x_4197_ = l_Lean_JsonNumber_fromInt(v_i_4193_);
                if v_isShared_4196_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4195_, 2);
                    leanh::lean_ctor_set(v___x_4195_, 0, v___x_4197_);
                    v___x_4199_ = v___x_4195_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
                    v___x_4199_ = v_reuseFailAlloc_4200_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_4187_ = v___x_4199_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_4205_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4204_, 3);
                    v___x_4207_ = v___x_4204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_s_4202_);
                    v___x_4207_ = v_reuseFailAlloc_4208_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4187_ = v___x_4207_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(
    mut v_k_4210_: *mut leanh::LeanObject,
    mut v_x_4211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4211_) == 0 {
                    leanh::lean_dec_ref(v_k_4210_);
                    v___x_4212_ = leanh::lean_box(0);
                    return v___x_4212_;
                } else {
                    v_val_4213_ = leanh::lean_ctor_get(v_x_4211_, 0);
                    v_isSharedCheck_4223_ = (!leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4223_ == 0 {
                        v___x_4215_ = v_x_4211_;
                        v_isShared_4216_ = v_isSharedCheck_4223_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4213_);
                        leanh::lean_dec(v_x_4211_);
                        v___x_4215_ = leanh::lean_box(0);
                        v_isShared_4216_ = v_isSharedCheck_4223_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4216_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4215_, 3);
                    v___x_4218_ = v___x_4215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4222_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_val_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4219_, 0, v_k_4210_);
                leanh::lean_ctor_set(v___x_4219_, 1, v___x_4218_);
                v___x_4220_ = leanh::lean_box(0);
                v___x_4221_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4221_, 0, v___x_4219_);
                leanh::lean_ctor_set(v___x_4221_, 1, v___x_4220_);
                return v___x_4221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__10(
    mut v_k_4224_: *mut leanh::LeanObject,
    mut v_x_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4225_) == 0 {
        let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4224_);
        v___x_4226_ = leanh::lean_box(0);
        return v___x_4226_;
    } else {
        let mut v_val_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4227_ = leanh::lean_ctor_get(v_x_4225_, 0);
        leanh::lean_inc(v_val_4227_);
        v___x_4228_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4228_, 0, v_k_4224_);
        leanh::lean_ctor_set(v___x_4228_, 1, v_val_4227_);
        v___x_4229_ = leanh::lean_box(0);
        v___x_4230_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4230_, 0, v___x_4228_);
        leanh::lean_ctor_set(v___x_4230_, 1, v___x_4229_);
        return v___x_4230_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__10___boxed(
    mut v_k_4231_: *mut leanh::LeanObject,
    mut v_x_4232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4233_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__10(v_k_4231_, v_x_4232_);
    leanh::lean_dec(v_x_4232_);
    return v_res_4233_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(
    mut v_a_4234_: *mut leanh::LeanObject,
    mut v_a_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4234_) == 0 {
                    v___x_4236_ = lean_array_to_list(v_a_4235_);
                    return v___x_4236_;
                } else {
                    v_head_4237_ = leanh::lean_ctor_get(v_a_4234_, 0);
                    leanh::lean_inc(v_head_4237_);
                    v_tail_4238_ = leanh::lean_ctor_get(v_a_4234_, 1);
                    leanh::lean_inc(v_tail_4238_);
                    leanh::lean_dec_ref_known(v_a_4234_, 2);
                    v___x_4239_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_4235_,
                        v_head_4237_,
                    );
                    v_a_4234_ = v_tail_4238_;
                    v_a_4235_ = v___x_4239_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7_spec__10_spec__14(
    mut v_sz_4241_: usize,
    mut v_i_4242_: usize,
    mut v_bs_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4244_: u8 = 0;
    let mut v_v_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: usize = 0;
    let mut v___x_4251_: usize = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4244_ = lean_usize_dec_lt(v_i_4242_, v_sz_4241_);
                if v___x_4244_ == 0 {
                    return v_bs_4243_;
                } else {
                    v_v_4245_ = lean_array_uget(v_bs_4243_, v_i_4242_);
                    v___x_4246_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4247_ = lean_array_uset(v_bs_4243_, v_i_4242_, v___x_4246_);
                    v___x_4254_ = (leanh::lean_unbox(v_v_4245_) as u8);
                    leanh::lean_dec(v_v_4245_);
                    if v___x_4254_ == 0 {
                        v___x_4255_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1);
                        v___y_4249_ = v___x_4255_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4256_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3);
                        v___y_4249_ = v___x_4256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4250_ = 1usize;
                v___x_4251_ = lean_usize_add(v_i_4242_, v___x_4250_);
                leanh::lean_inc(v___y_4249_);
                v___x_4252_ = lean_array_uset(v_bs_x27_4247_, v_i_4242_, v___y_4249_);
                v_i_4242_ = v___x_4251_;
                v_bs_4243_ = v___x_4252_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7_spec__10_spec__14___boxed(
    mut v_sz_4257_: *mut leanh::LeanObject,
    mut v_i_4258_: *mut leanh::LeanObject,
    mut v_bs_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4260_: usize = 0;
    let mut v_i_boxed_4261_: usize = 0;
    let mut v_res_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4260_ = leanh::lean_unbox_usize(v_sz_4257_);
    leanh::lean_dec(v_sz_4257_);
    v_i_boxed_4261_ = leanh::lean_unbox_usize(v_i_4258_);
    leanh::lean_dec(v_i_4258_);
    v_res_4262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7_spec__10_spec__14(v_sz_boxed_4260_, v_i_boxed_4261_, v_bs_4259_);
    return v_res_4262_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7_spec__10(
    mut v_a_4263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4264_: usize = 0;
    let mut v___x_4265_: usize = 0;
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4264_ = lean_array_size(v_a_4263_);
    v___x_4265_ = 0usize;
    v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7_spec__10_spec__14(v_sz_4264_, v___x_4265_, v_a_4263_);
    v___x_4267_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4267_, 0, v___x_4266_);
    return v___x_4267_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7(
    mut v_k_4268_: *mut leanh::LeanObject,
    mut v_x_4269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4269_) == 0 {
        let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4268_);
        v___x_4270_ = leanh::lean_box(0);
        return v___x_4270_;
    } else {
        let mut v_val_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4271_ = leanh::lean_ctor_get(v_x_4269_, 0);
        leanh::lean_inc(v_val_4271_);
        leanh::lean_dec_ref_known(v_x_4269_, 1);
        v___x_4272_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7_spec__10(v_val_4271_);
        v___x_4273_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4273_, 0, v_k_4268_);
        leanh::lean_ctor_set(v___x_4273_, 1, v___x_4272_);
        v___x_4274_ = leanh::lean_box(0);
        v___x_4275_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4275_, 0, v___x_4273_);
        leanh::lean_ctor_set(v___x_4275_, 1, v___x_4274_);
        return v___x_4275_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__2(
    mut v_k_4276_: *mut leanh::LeanObject,
    mut v_x_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4277_) == 0 {
        let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4276_);
        v___x_4278_ = leanh::lean_box(0);
        return v___x_4278_;
    } else {
        let mut v_val_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4279_ = leanh::lean_ctor_get(v_x_4277_, 0);
        leanh::lean_inc(v_val_4279_);
        leanh::lean_dec_ref_known(v_x_4277_, 1);
        v___x_4280_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_4279_);
        v___x_4281_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4281_, 0, v_k_4276_);
        leanh::lean_ctor_set(v___x_4281_, 1, v___x_4280_);
        v___x_4282_ = leanh::lean_box(0);
        v___x_4283_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4283_, 0, v___x_4281_);
        leanh::lean_ctor_set(v___x_4283_, 1, v___x_4282_);
        return v___x_4283_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8_spec__12_spec__17(
    mut v_sz_4284_: usize,
    mut v_i_4285_: usize,
    mut v_bs_4286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4287_: u8 = 0;
    let mut v_v_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: usize = 0;
    let mut v___x_4294_: usize = 0;
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: u8 = 0;
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4287_ = lean_usize_dec_lt(v_i_4285_, v_sz_4284_);
                if v___x_4287_ == 0 {
                    return v_bs_4286_;
                } else {
                    v_v_4288_ = lean_array_uget(v_bs_4286_, v_i_4285_);
                    v___x_4289_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4290_ = lean_array_uset(v_bs_4286_, v_i_4285_, v___x_4289_);
                    v___x_4297_ = (leanh::lean_unbox(v_v_4288_) as u8);
                    leanh::lean_dec(v_v_4288_);
                    if v___x_4297_ == 0 {
                        v___x_4298_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1);
                        v___y_4292_ = v___x_4298_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3);
                        v___y_4292_ = v___x_4299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4293_ = 1usize;
                v___x_4294_ = lean_usize_add(v_i_4285_, v___x_4293_);
                leanh::lean_inc(v___y_4292_);
                v___x_4295_ = lean_array_uset(v_bs_x27_4290_, v_i_4285_, v___y_4292_);
                v_i_4285_ = v___x_4294_;
                v_bs_4286_ = v___x_4295_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8_spec__12_spec__17___boxed(
    mut v_sz_4300_: *mut leanh::LeanObject,
    mut v_i_4301_: *mut leanh::LeanObject,
    mut v_bs_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4303_: usize = 0;
    let mut v_i_boxed_4304_: usize = 0;
    let mut v_res_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4303_ = leanh::lean_unbox_usize(v_sz_4300_);
    leanh::lean_dec(v_sz_4300_);
    v_i_boxed_4304_ = leanh::lean_unbox_usize(v_i_4301_);
    leanh::lean_dec(v_i_4301_);
    v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8_spec__12_spec__17(v_sz_boxed_4303_, v_i_boxed_4304_, v_bs_4302_);
    return v_res_4305_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8_spec__12(
    mut v_a_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4307_: usize = 0;
    let mut v___x_4308_: usize = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4307_ = lean_array_size(v_a_4306_);
    v___x_4308_ = 0usize;
    v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8_spec__12_spec__17(v_sz_4307_, v___x_4308_, v_a_4306_);
    v___x_4310_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4310_, 0, v___x_4309_);
    return v___x_4310_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8(
    mut v_k_4311_: *mut leanh::LeanObject,
    mut v_x_4312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4312_) == 0 {
        let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4311_);
        v___x_4313_ = leanh::lean_box(0);
        return v___x_4313_;
    } else {
        let mut v_val_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4314_ = leanh::lean_ctor_get(v_x_4312_, 0);
        leanh::lean_inc(v_val_4314_);
        leanh::lean_dec_ref_known(v_x_4312_, 1);
        v___x_4315_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8_spec__12(v_val_4314_);
        v___x_4316_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4316_, 0, v_k_4311_);
        leanh::lean_ctor_set(v___x_4316_, 1, v___x_4315_);
        v___x_4317_ = leanh::lean_box(0);
        v___x_4318_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4318_, 0, v___x_4316_);
        leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
        return v___x_4318_;
    }
}
pub unsafe fn _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4319_ = leanh::lean_unsigned_to_nat(3);
    v___x_4320_ = l_Lean_JsonNumber_fromNat(v___x_4319_);
    return v___x_4320_;
}
pub unsafe fn _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__0_once), _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__0);
    v___x_4322_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4322_, 0, v___x_4321_);
    return v___x_4322_;
}
pub unsafe fn _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ = leanh::lean_unsigned_to_nat(4);
    v___x_4324_ = l_Lean_JsonNumber_fromNat(v___x_4323_);
    return v___x_4324_;
}
pub unsafe fn _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4325_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__2_once), _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__2);
    v___x_4326_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4326_, 0, v___x_4325_);
    return v___x_4326_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3(
    mut v_k_4327_: *mut leanh::LeanObject,
    mut v_x_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4328_) == 0 {
                    leanh::lean_dec_ref(v_k_4327_);
                    v___x_4334_ = leanh::lean_box(0);
                    return v___x_4334_;
                } else {
                    v_val_4335_ = leanh::lean_ctor_get(v_x_4328_, 0);
                    v___x_4336_ = (leanh::lean_unbox(v_val_4335_) as u8);
                    match v___x_4336_ {
                        0 => {
                            v___x_4337_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__1);
                            v___y_4330_ = v___x_4337_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_4338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3_once), _init_l_Lean_Lsp_instToJsonCodeActionTriggerKind___lam__0___closed__3);
                            v___y_4330_ = v___x_4338_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___x_4339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__1_once), _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__1);
                            v___y_4330_ = v___x_4339_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_4340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__3_once), _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___closed__3);
                            v___y_4330_ = v___x_4340_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_4330_);
                v___x_4331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4331_, 0, v_k_4327_);
                leanh::lean_ctor_set(v___x_4331_, 1, v___y_4330_);
                v___x_4332_ = leanh::lean_box(0);
                v___x_4333_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4333_, 0, v___x_4331_);
                leanh::lean_ctor_set(v___x_4333_, 1, v___x_4332_);
                return v___x_4333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3___boxed(
    mut v_k_4341_: *mut leanh::LeanObject,
    mut v_x_4342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3(v_k_4341_, v_x_4342_);
    leanh::lean_dec(v_x_4342_);
    return v_res_4343_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(
    mut v_k_4344_: *mut leanh::LeanObject,
    mut v_x_4345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4345_) == 0 {
        let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4344_);
        v___x_4346_ = leanh::lean_box(0);
        return v___x_4346_;
    } else {
        let mut v_val_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4349_: u8 = 0;
        let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4347_ = leanh::lean_ctor_get(v_x_4345_, 0);
        v___x_4348_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
        v___x_4349_ = (leanh::lean_unbox(v_val_4347_) as u8);
        leanh::lean_ctor_set_uint8(v___x_4348_, 0 as u32, v___x_4349_);
        v___x_4350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4350_, 0, v_k_4344_);
        leanh::lean_ctor_set(v___x_4350_, 1, v___x_4348_);
        v___x_4351_ = leanh::lean_box(0);
        v___x_4352_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4352_, 0, v___x_4350_);
        leanh::lean_ctor_set(v___x_4352_, 1, v___x_4351_);
        return v___x_4352_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4___boxed(
    mut v_k_4353_: *mut leanh::LeanObject,
    mut v_x_4354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4355_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v_k_4353_, v_x_4354_);
    leanh::lean_dec(v_x_4354_);
    return v_res_4355_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0(
    mut v_x_4358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_4359_ = leanh::lean_ctor_get(v_x_4358_, 0);
    leanh::lean_inc_ref(v_range_4359_);
    v_fullRange_x3f_4360_ = leanh::lean_ctor_get(v_x_4358_, 1);
    leanh::lean_inc(v_fullRange_x3f_4360_);
    v_severity_x3f_4361_ = leanh::lean_ctor_get(v_x_4358_, 2);
    leanh::lean_inc(v_severity_x3f_4361_);
    v_isSilent_x3f_4362_ = leanh::lean_ctor_get(v_x_4358_, 3);
    leanh::lean_inc(v_isSilent_x3f_4362_);
    v_code_x3f_4363_ = leanh::lean_ctor_get(v_x_4358_, 4);
    leanh::lean_inc(v_code_x3f_4363_);
    v_source_x3f_4364_ = leanh::lean_ctor_get(v_x_4358_, 5);
    leanh::lean_inc(v_source_x3f_4364_);
    v_message_4365_ = leanh::lean_ctor_get(v_x_4358_, 6);
    leanh::lean_inc(v_message_4365_);
    v_tags_x3f_4366_ = leanh::lean_ctor_get(v_x_4358_, 7);
    leanh::lean_inc(v_tags_x3f_4366_);
    v_leanTags_x3f_4367_ = leanh::lean_ctor_get(v_x_4358_, 8);
    leanh::lean_inc(v_leanTags_x3f_4367_);
    v_relatedInformation_x3f_4368_ = leanh::lean_ctor_get(v_x_4358_, 9);
    leanh::lean_inc(v_relatedInformation_x3f_4368_);
    v_data_x3f_4369_ = leanh::lean_ctor_get(v_x_4358_, 10);
    leanh::lean_inc(v_data_x3f_4369_);
    leanh::lean_dec_ref(v_x_4358_);
    v___x_4370_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0;
    v___x_4371_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_4359_);
    v___x_4372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4372_, 0, v___x_4370_);
    leanh::lean_ctor_set(v___x_4372_, 1, v___x_4371_);
    v___x_4373_ = leanh::lean_box(0);
    v___x_4374_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4374_, 0, v___x_4372_);
    leanh::lean_ctor_set(v___x_4374_, 1, v___x_4373_);
    v___x_4375_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__13;
    v___x_4376_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__2(v___x_4375_, v_fullRange_x3f_4360_);
    v___x_4377_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__19;
    v___x_4378_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__3(v___x_4377_, v_severity_x3f_4361_);
    leanh::lean_dec(v_severity_x3f_4361_);
    v___x_4379_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__25;
    v___x_4380_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_4379_, v_isSilent_x3f_4362_);
    leanh::lean_dec(v_isSilent_x3f_4362_);
    v___x_4381_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__31;
    v___x_4382_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__5(v___x_4381_, v_code_x3f_4363_);
    v___x_4383_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__37;
    v___x_4384_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(v___x_4383_, v_source_x3f_4364_);
    v___x_4385_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__43;
    v___x_4386_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4386_, 0, v_message_4365_);
    v___x_4387_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4387_, 0, v___x_4385_);
    leanh::lean_ctor_set(v___x_4387_, 1, v___x_4386_);
    v___x_4388_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4388_, 0, v___x_4387_);
    leanh::lean_ctor_set(v___x_4388_, 1, v___x_4373_);
    v___x_4389_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__48;
    v___x_4390_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__7(v___x_4389_, v_tags_x3f_4366_);
    v___x_4391_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__54;
    v___x_4392_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__8(v___x_4391_, v_leanTags_x3f_4367_);
    v___x_4393_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__60;
    v___x_4394_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__9(v___x_4393_, v_relatedInformation_x3f_4368_);
    v___x_4395_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66;
    v___x_4396_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__10(v___x_4395_, v_data_x3f_4369_);
    leanh::lean_dec(v_data_x3f_4369_);
    v___x_4397_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4397_, 0, v___x_4396_);
    leanh::lean_ctor_set(v___x_4397_, 1, v___x_4373_);
    v___x_4398_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4398_, 0, v___x_4394_);
    leanh::lean_ctor_set(v___x_4398_, 1, v___x_4397_);
    v___x_4399_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4399_, 0, v___x_4392_);
    leanh::lean_ctor_set(v___x_4399_, 1, v___x_4398_);
    v___x_4400_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4400_, 0, v___x_4390_);
    leanh::lean_ctor_set(v___x_4400_, 1, v___x_4399_);
    v___x_4401_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4401_, 0, v___x_4388_);
    leanh::lean_ctor_set(v___x_4401_, 1, v___x_4400_);
    v___x_4402_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4384_);
    leanh::lean_ctor_set(v___x_4402_, 1, v___x_4401_);
    v___x_4403_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4403_, 0, v___x_4382_);
    leanh::lean_ctor_set(v___x_4403_, 1, v___x_4402_);
    v___x_4404_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4404_, 0, v___x_4380_);
    leanh::lean_ctor_set(v___x_4404_, 1, v___x_4403_);
    v___x_4405_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4405_, 0, v___x_4378_);
    leanh::lean_ctor_set(v___x_4405_, 1, v___x_4404_);
    v___x_4406_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4406_, 0, v___x_4376_);
    leanh::lean_ctor_set(v___x_4406_, 1, v___x_4405_);
    v___x_4407_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4407_, 0, v___x_4374_);
    leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
    v___x_4408_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_4409_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_4407_, v___x_4408_);
    v___x_4410_ = l_Lean_Json_mkObj(v___x_4409_);
    leanh::lean_dec(v___x_4409_);
    return v___x_4410_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__1(
    mut v_sz_4411_: usize,
    mut v_i_4412_: usize,
    mut v_bs_4413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4414_: u8 = 0;
    let mut v_v_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: usize = 0;
    let mut v___x_4420_: usize = 0;
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4414_ = lean_usize_dec_lt(v_i_4412_, v_sz_4411_);
                if v___x_4414_ == 0 {
                    return v_bs_4413_;
                } else {
                    v_v_4415_ = lean_array_uget(v_bs_4413_, v_i_4412_);
                    v___x_4416_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4417_ = lean_array_uset(v_bs_4413_, v_i_4412_, v___x_4416_);
                    v___x_4418_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0(v_v_4415_);
                    v___x_4419_ = 1usize;
                    v___x_4420_ = lean_usize_add(v_i_4412_, v___x_4419_);
                    v___x_4421_ = lean_array_uset(v_bs_x27_4417_, v_i_4412_, v___x_4418_);
                    v_i_4412_ = v___x_4420_;
                    v_bs_4413_ = v___x_4421_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__1___boxed(
    mut v_sz_4423_: *mut leanh::LeanObject,
    mut v_i_4424_: *mut leanh::LeanObject,
    mut v_bs_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4426_: usize = 0;
    let mut v_i_boxed_4427_: usize = 0;
    let mut v_res_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4426_ = leanh::lean_unbox_usize(v_sz_4423_);
    leanh::lean_dec(v_sz_4423_);
    v_i_boxed_4427_ = leanh::lean_unbox_usize(v_i_4424_);
    leanh::lean_dec(v_i_4424_);
    v_res_4428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__1(v_sz_boxed_4426_, v_i_boxed_4427_, v_bs_4425_);
    return v_res_4428_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0(
    mut v_a_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4430_: usize = 0;
    let mut v___x_4431_: usize = 0;
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4430_ = lean_array_size(v_a_4429_);
    v___x_4431_ = 0usize;
    v___x_4432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__1(v_sz_4430_, v___x_4431_, v_a_4429_);
    v___x_4433_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4433_, 0, v___x_4432_);
    return v___x_4433_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3_spec__14(
    mut v_sz_4434_: usize,
    mut v_i_4435_: usize,
    mut v_bs_4436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4437_: u8 = 0;
    let mut v_v_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: usize = 0;
    let mut v___x_4443_: usize = 0;
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4437_ = lean_usize_dec_lt(v_i_4435_, v_sz_4434_);
                if v___x_4437_ == 0 {
                    return v_bs_4436_;
                } else {
                    v_v_4438_ = lean_array_uget(v_bs_4436_, v_i_4435_);
                    v___x_4439_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4440_ = lean_array_uset(v_bs_4436_, v_i_4435_, v___x_4439_);
                    v___x_4441_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4441_, 0, v_v_4438_);
                    v___x_4442_ = 1usize;
                    v___x_4443_ = lean_usize_add(v_i_4435_, v___x_4442_);
                    v___x_4444_ = lean_array_uset(v_bs_x27_4440_, v_i_4435_, v___x_4441_);
                    v_i_4435_ = v___x_4443_;
                    v_bs_4436_ = v___x_4444_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3_spec__14___boxed(
    mut v_sz_4446_: *mut leanh::LeanObject,
    mut v_i_4447_: *mut leanh::LeanObject,
    mut v_bs_4448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4449_: usize = 0;
    let mut v_i_boxed_4450_: usize = 0;
    let mut v_res_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4449_ = leanh::lean_unbox_usize(v_sz_4446_);
    leanh::lean_dec(v_sz_4446_);
    v_i_boxed_4450_ = leanh::lean_unbox_usize(v_i_4447_);
    leanh::lean_dec(v_i_4447_);
    v_res_4451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3_spec__14(v_sz_boxed_4449_, v_i_boxed_4450_, v_bs_4448_);
    return v_res_4451_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3(
    mut v_a_4452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4453_: usize = 0;
    let mut v___x_4454_: usize = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4453_ = lean_array_size(v_a_4452_);
    v___x_4454_ = 0usize;
    v___x_4455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3_spec__14(v_sz_4453_, v___x_4454_, v_a_4452_);
    v___x_4456_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4456_, 0, v___x_4455_);
    return v___x_4456_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1(
    mut v_k_4457_: *mut leanh::LeanObject,
    mut v_x_4458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4458_) == 0 {
        let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4457_);
        v___x_4459_ = leanh::lean_box(0);
        return v___x_4459_;
    } else {
        let mut v_val_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4460_ = leanh::lean_ctor_get(v_x_4458_, 0);
        leanh::lean_inc(v_val_4460_);
        leanh::lean_dec_ref_known(v_x_4458_, 1);
        v___x_4461_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3(v_val_4460_);
        v___x_4462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4462_, 0, v_k_4457_);
        leanh::lean_ctor_set(v___x_4462_, 1, v___x_4461_);
        v___x_4463_ = leanh::lean_box(0);
        v___x_4464_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4464_, 0, v___x_4462_);
        leanh::lean_ctor_set(v___x_4464_, 1, v___x_4463_);
        return v___x_4464_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionContext_toJson(
    mut v_x_4465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diagnostics_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_only_x3f_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_triggerKind_x3f_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_diagnostics_4466_ = leanh::lean_ctor_get(v_x_4465_, 0);
    leanh::lean_inc_ref(v_diagnostics_4466_);
    v_only_x3f_4467_ = leanh::lean_ctor_get(v_x_4465_, 1);
    leanh::lean_inc(v_only_x3f_4467_);
    v_triggerKind_x3f_4468_ = leanh::lean_ctor_get(v_x_4465_, 2);
    leanh::lean_inc(v_triggerKind_x3f_4468_);
    leanh::lean_dec_ref(v_x_4465_);
    v___x_4469_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0;
    v___x_4470_ = l_Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0(
        v_diagnostics_4466_,
    );
    v___x_4471_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4471_, 0, v___x_4469_);
    leanh::lean_ctor_set(v___x_4471_, 1, v___x_4470_);
    v___x_4472_ = leanh::lean_box(0);
    v___x_4473_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4473_, 0, v___x_4471_);
    leanh::lean_ctor_set(v___x_4473_, 1, v___x_4472_);
    v___x_4474_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__9;
    v___x_4475_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1(
        v___x_4474_,
        v_only_x3f_4467_,
    );
    v___x_4476_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__15;
    v___x_4477_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__2(
        v___x_4476_,
        v_triggerKind_x3f_4468_,
    );
    leanh::lean_dec(v_triggerKind_x3f_4468_);
    v___x_4478_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4478_, 0, v___x_4477_);
    leanh::lean_ctor_set(v___x_4478_, 1, v___x_4472_);
    v___x_4479_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4479_, 0, v___x_4475_);
    leanh::lean_ctor_set(v___x_4479_, 1, v___x_4478_);
    v___x_4480_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4480_, 0, v___x_4473_);
    leanh::lean_ctor_set(v___x_4480_, 1, v___x_4479_);
    v___x_4481_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_4482_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_4480_, v___x_4481_);
    v___x_4483_ = l_Lean_Json_mkObj(v___x_4482_);
    leanh::lean_dec(v___x_4482_);
    return v___x_4483_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__0(
    mut v_j_4486_: *mut leanh::LeanObject,
    mut v_k_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = l_Lean_Json_getObjValD(v_j_4486_, v_k_4487_);
    v___x_4489_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_4488_);
    return v___x_4489_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__0___boxed(
    mut v_j_4490_: *mut leanh::LeanObject,
    mut v_k_4491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4492_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__0(
            v_j_4490_, v_k_4491_,
        );
    leanh::lean_dec_ref(v_k_4491_);
    return v_res_4492_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__1(
    mut v_j_4493_: *mut leanh::LeanObject,
    mut v_k_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4495_ = l_Lean_Json_getObjValD(v_j_4493_, v_k_4494_);
    v___x_4496_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson(v___x_4495_);
    return v___x_4496_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__1___boxed(
    mut v_j_4497_: *mut leanh::LeanObject,
    mut v_k_4498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4499_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__1(
            v_j_4497_, v_k_4498_,
        );
    leanh::lean_dec_ref(v_k_4498_);
    return v_res_4499_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4506_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4506_ = 1;
    v___x_4507_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__2;
    v___x_4508_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4507_, v___x_4506_);
    return v___x_4508_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4509_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_4510_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__3,
    );
    v___x_4511_ = lean_string_append(v___x_4510_, v___x_4509_);
    return v___x_4511_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4515_: u8 = 0;
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4515_ = 1;
    v___x_4516_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__6;
    v___x_4517_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4516_, v___x_4515_);
    return v___x_4517_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4518_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7,
    );
    v___x_4519_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4,
    );
    v___x_4520_ = lean_string_append(v___x_4519_, v___x_4518_);
    return v___x_4520_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4522_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__8,
    );
    v___x_4523_ = lean_string_append(v___x_4522_, v___x_4521_);
    return v___x_4523_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4528_: u8 = 0;
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4528_ = 1;
    v___x_4529_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__12;
    v___x_4530_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4529_, v___x_4528_);
    return v___x_4530_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13,
    );
    v___x_4532_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4,
    );
    v___x_4533_ = lean_string_append(v___x_4532_, v___x_4531_);
    return v___x_4533_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4534_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__14,
    );
    v___x_4536_ = lean_string_append(v___x_4535_, v___x_4534_);
    return v___x_4536_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4540_: u8 = 0;
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4540_ = 1;
    v___x_4541_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__17;
    v___x_4542_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4541_, v___x_4540_);
    return v___x_4542_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4543_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__18_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__18,
    );
    v___x_4544_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4,
    );
    v___x_4545_ = lean_string_append(v___x_4544_, v___x_4543_);
    return v___x_4545_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4547_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__19_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__19,
    );
    v___x_4548_ = lean_string_append(v___x_4547_, v___x_4546_);
    return v___x_4548_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4549_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9_once), _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__9);
    v___x_4550_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4,
    );
    v___x_4551_ = lean_string_append(v___x_4550_, v___x_4549_);
    return v___x_4551_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4552_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4553_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__21_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__21,
    );
    v___x_4554_ = lean_string_append(v___x_4553_, v___x_4552_);
    return v___x_4554_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = 1;
    v___x_4559_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__24;
    v___x_4560_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4559_, v___x_4558_);
    return v___x_4560_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4561_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__25_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__25,
    );
    v___x_4562_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__4,
    );
    v___x_4563_ = lean_string_append(v___x_4562_, v___x_4561_);
    return v___x_4563_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4564_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4565_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__26_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__26,
    );
    v___x_4566_ = lean_string_append(v___x_4565_, v___x_4564_);
    return v___x_4566_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(
    mut v_json_4567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4573_: u8 = 0;
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v_a_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_a_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v_a_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v_a_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4615_: u8 = 0;
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v_a_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4625_: u8 = 0;
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4629_: u8 = 0;
    let mut v_a_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_a_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut v_a_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4657_: u8 = 0;
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4663_: u8 = 0;
    let mut v_a_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4667_: u8 = 0;
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4671_: u8 = 0;
    let mut v_a_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4568_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0;
                leanh::lean_inc(v_json_4567_);
                v___x_4569_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_json_4567_, v___x_4568_);
                if leanh::lean_obj_tag(v___x_4569_) == 0 {
                    leanh::lean_dec(v_json_4567_);
                    v_a_4570_ = leanh::lean_ctor_get(v___x_4569_, 0);
                    v_isSharedCheck_4579_ = (!leanh::lean_is_exclusive(v___x_4569_)) as u8;
                    if v_isSharedCheck_4579_ == 0 {
                        v___x_4572_ = v___x_4569_;
                        v_isShared_4573_ = v_isSharedCheck_4579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4570_);
                        leanh::lean_dec(v___x_4569_);
                        v___x_4572_ = leanh::lean_box(0);
                        v_isShared_4573_ = v_isSharedCheck_4579_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_4569_) == 0 {
                        leanh::lean_dec(v_json_4567_);
                        v_a_4580_ = leanh::lean_ctor_get(v___x_4569_, 0);
                        v_isSharedCheck_4587_ =
                            (!leanh::lean_is_exclusive(v___x_4569_)) as u8;
                        if v_isSharedCheck_4587_ == 0 {
                            v___x_4582_ = v___x_4569_;
                            v_isShared_4583_ = v_isSharedCheck_4587_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4580_);
                            leanh::lean_dec(v___x_4569_);
                            v___x_4582_ = leanh::lean_box(0);
                            v_isShared_4583_ = v_isSharedCheck_4587_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4588_ = leanh::lean_ctor_get(v___x_4569_, 0);
                        leanh::lean_inc(v_a_4588_);
                        leanh::lean_dec_ref_known(v___x_4569_, 1);
                        v___x_4589_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10;
                        leanh::lean_inc(v_json_4567_);
                        v___x_4590_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_json_4567_, v___x_4589_);
                        if leanh::lean_obj_tag(v___x_4590_) == 0 {
                            leanh::lean_dec(v_a_4588_);
                            leanh::lean_dec(v_json_4567_);
                            v_a_4591_ = leanh::lean_ctor_get(v___x_4590_, 0);
                            v_isSharedCheck_4600_ =
                                (!leanh::lean_is_exclusive(v___x_4590_)) as u8;
                            if v_isSharedCheck_4600_ == 0 {
                                v___x_4593_ = v___x_4590_;
                                v_isShared_4594_ = v_isSharedCheck_4600_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4591_);
                                leanh::lean_dec(v___x_4590_);
                                v___x_4593_ = leanh::lean_box(0);
                                v_isShared_4594_ = v_isSharedCheck_4600_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_4590_) == 0 {
                                leanh::lean_dec(v_a_4588_);
                                leanh::lean_dec(v_json_4567_);
                                v_a_4601_ = leanh::lean_ctor_get(v___x_4590_, 0);
                                v_isSharedCheck_4608_ =
                                    (!leanh::lean_is_exclusive(v___x_4590_)) as u8;
                                if v_isSharedCheck_4608_ == 0 {
                                    v___x_4603_ = v___x_4590_;
                                    v_isShared_4604_ = v_isSharedCheck_4608_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4601_);
                                    leanh::lean_dec(v___x_4590_);
                                    v___x_4603_ = leanh::lean_box(0);
                                    v_isShared_4604_ = v_isSharedCheck_4608_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4609_ = leanh::lean_ctor_get(v___x_4590_, 0);
                                leanh::lean_inc(v_a_4609_);
                                leanh::lean_dec_ref_known(v___x_4590_, 1);
                                v___x_4610_ =
                                    l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__16;
                                leanh::lean_inc(v_json_4567_);
                                v___x_4611_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__0(v_json_4567_, v___x_4610_);
                                if leanh::lean_obj_tag(v___x_4611_) == 0 {
                                    leanh::lean_dec(v_a_4609_);
                                    leanh::lean_dec(v_a_4588_);
                                    leanh::lean_dec(v_json_4567_);
                                    v_a_4612_ = leanh::lean_ctor_get(v___x_4611_, 0);
                                    v_isSharedCheck_4621_ =
                                        (!leanh::lean_is_exclusive(v___x_4611_)) as u8;
                                    if v_isSharedCheck_4621_ == 0 {
                                        v___x_4614_ = v___x_4611_;
                                        v_isShared_4615_ = v_isSharedCheck_4621_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4612_);
                                        leanh::lean_dec(v___x_4611_);
                                        v___x_4614_ = leanh::lean_box(0);
                                        v_isShared_4615_ = v_isSharedCheck_4621_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_4611_) == 0 {
                                        leanh::lean_dec(v_a_4609_);
                                        leanh::lean_dec(v_a_4588_);
                                        leanh::lean_dec(v_json_4567_);
                                        v_a_4622_ = leanh::lean_ctor_get(v___x_4611_, 0);
                                        v_isSharedCheck_4629_ =
                                            (!leanh::lean_is_exclusive(v___x_4611_)) as u8;
                                        if v_isSharedCheck_4629_ == 0 {
                                            v___x_4624_ = v___x_4611_;
                                            v_isShared_4625_ = v_isSharedCheck_4629_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4622_);
                                            leanh::lean_dec(v___x_4611_);
                                            v___x_4624_ = leanh::lean_box(0);
                                            v_isShared_4625_ = v_isSharedCheck_4629_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4630_ = leanh::lean_ctor_get(v___x_4611_, 0);
                                        leanh::lean_inc(v_a_4630_);
                                        leanh::lean_dec_ref_known(v___x_4611_, 1);
                                        v___x_4631_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0;
                                        leanh::lean_inc(v_json_4567_);
                                        v___x_4632_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__5(v_json_4567_, v___x_4631_);
                                        if leanh::lean_obj_tag(v___x_4632_) == 0 {
                                            leanh::lean_dec(v_a_4630_);
                                            leanh::lean_dec(v_a_4609_);
                                            leanh::lean_dec(v_a_4588_);
                                            leanh::lean_dec(v_json_4567_);
                                            v_a_4633_ = leanh::lean_ctor_get(v___x_4632_, 0);
                                            v_isSharedCheck_4642_ =
                                                (!leanh::lean_is_exclusive(v___x_4632_))
                                                    as u8;
                                            if v_isSharedCheck_4642_ == 0 {
                                                v___x_4635_ = v___x_4632_;
                                                v_isShared_4636_ = v_isSharedCheck_4642_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4633_);
                                                leanh::lean_dec(v___x_4632_);
                                                v___x_4635_ = leanh::lean_box(0);
                                                v_isShared_4636_ = v_isSharedCheck_4642_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_4632_) == 0 {
                                                leanh::lean_dec(v_a_4630_);
                                                leanh::lean_dec(v_a_4609_);
                                                leanh::lean_dec(v_a_4588_);
                                                leanh::lean_dec(v_json_4567_);
                                                v_a_4643_ =
                                                    leanh::lean_ctor_get(v___x_4632_, 0);
                                                v_isSharedCheck_4650_ =
                                                    (!leanh::lean_is_exclusive(v___x_4632_))
                                                        as u8;
                                                if v_isSharedCheck_4650_ == 0 {
                                                    v___x_4645_ = v___x_4632_;
                                                    v_isShared_4646_ = v_isSharedCheck_4650_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4643_);
                                                    leanh::lean_dec(v___x_4632_);
                                                    v___x_4645_ = leanh::lean_box(0);
                                                    v_isShared_4646_ = v_isSharedCheck_4650_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_4651_ =
                                                    leanh::lean_ctor_get(v___x_4632_, 0);
                                                leanh::lean_inc(v_a_4651_);
                                                leanh::lean_dec_ref_known(v___x_4632_, 1);
                                                v___x_4652_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__23;
                                                v___x_4653_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionParams_fromJson_spec__1(v_json_4567_, v___x_4652_);
                                                if leanh::lean_obj_tag(v___x_4653_) == 0 {
                                                    leanh::lean_dec(v_a_4651_);
                                                    leanh::lean_dec(v_a_4630_);
                                                    leanh::lean_dec(v_a_4609_);
                                                    leanh::lean_dec(v_a_4588_);
                                                    v_a_4654_ =
                                                        leanh::lean_ctor_get(v___x_4653_, 0);
                                                    v_isSharedCheck_4663_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4653_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4663_ == 0 {
                                                        v___x_4656_ = v___x_4653_;
                                                        v_isShared_4657_ = v_isSharedCheck_4663_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4654_);
                                                        leanh::lean_dec(v___x_4653_);
                                                        v___x_4656_ = leanh::lean_box(0);
                                                        v_isShared_4657_ = v_isSharedCheck_4663_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_4653_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_4651_);
                                                        leanh::lean_dec(v_a_4630_);
                                                        leanh::lean_dec(v_a_4609_);
                                                        leanh::lean_dec(v_a_4588_);
                                                        v_a_4664_ = leanh::lean_ctor_get(
                                                            v___x_4653_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4671_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_4653_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4671_ == 0 {
                                                            v___x_4666_ = v___x_4653_;
                                                            v_isShared_4667_ =
                                                                v_isSharedCheck_4671_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_4664_);
                                                            leanh::lean_dec(v___x_4653_);
                                                            v___x_4666_ = leanh::lean_box(0);
                                                            v_isShared_4667_ =
                                                                v_isSharedCheck_4671_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_4672_ = leanh::lean_ctor_get(
                                                            v___x_4653_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4680_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_4653_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4680_ == 0 {
                                                            v___x_4674_ = v___x_4653_;
                                                            v_isShared_4675_ =
                                                                v_isSharedCheck_4680_;
                                                            state = 21;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_4672_);
                                                            leanh::lean_dec(v___x_4653_);
                                                            v___x_4674_ = leanh::lean_box(0);
                                                            v_isShared_4675_ =
                                                                v_isSharedCheck_4680_;
                                                            state = 21;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4574_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__9,
                );
                v___x_4575_ = lean_string_append(v___x_4574_, v_a_4570_);
                leanh::lean_dec(v_a_4570_);
                if v_isShared_4573_ == 0 {
                    leanh::lean_ctor_set(v___x_4572_, 0, v___x_4575_);
                    v___x_4577_ = v___x_4572_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4578_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4575_);
                    v___x_4577_ = v_reuseFailAlloc_4578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4577_;
            }
            3 => {
                if v_isShared_4583_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4582_, 0);
                    v___x_4585_ = v___x_4582_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
                    v___x_4585_ = v_reuseFailAlloc_4586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4585_;
            }
            5 => {
                v___x_4595_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__15,
                );
                v___x_4596_ = lean_string_append(v___x_4595_, v_a_4591_);
                leanh::lean_dec(v_a_4591_);
                if v_isShared_4594_ == 0 {
                    leanh::lean_ctor_set(v___x_4593_, 0, v___x_4596_);
                    v___x_4598_ = v___x_4593_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
                    v___x_4598_ = v_reuseFailAlloc_4599_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4598_;
            }
            7 => {
                if v_isShared_4604_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4603_, 0);
                    v___x_4606_ = v___x_4603_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
                    v___x_4606_ = v_reuseFailAlloc_4607_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4606_;
            }
            9 => {
                v___x_4616_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__20_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__20,
                );
                v___x_4617_ = lean_string_append(v___x_4616_, v_a_4612_);
                leanh::lean_dec(v_a_4612_);
                if v_isShared_4615_ == 0 {
                    leanh::lean_ctor_set(v___x_4614_, 0, v___x_4617_);
                    v___x_4619_ = v___x_4614_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4619_;
            }
            11 => {
                if v_isShared_4625_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4624_, 0);
                    v___x_4627_ = v___x_4624_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4628_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
                    v___x_4627_ = v_reuseFailAlloc_4628_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4627_;
            }
            13 => {
                v___x_4637_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__22_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__22,
                );
                v___x_4638_ = lean_string_append(v___x_4637_, v_a_4633_);
                leanh::lean_dec(v_a_4633_);
                if v_isShared_4636_ == 0 {
                    leanh::lean_ctor_set(v___x_4635_, 0, v___x_4638_);
                    v___x_4640_ = v___x_4635_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4641_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
                    v___x_4640_ = v_reuseFailAlloc_4641_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4640_;
            }
            15 => {
                if v_isShared_4646_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4645_, 0);
                    v___x_4648_ = v___x_4645_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
                    v___x_4648_ = v_reuseFailAlloc_4649_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4648_;
            }
            17 => {
                v___x_4658_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__27_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__27,
                );
                v___x_4659_ = lean_string_append(v___x_4658_, v_a_4654_);
                leanh::lean_dec(v_a_4654_);
                if v_isShared_4657_ == 0 {
                    leanh::lean_ctor_set(v___x_4656_, 0, v___x_4659_);
                    v___x_4661_ = v___x_4656_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
                    v___x_4661_ = v_reuseFailAlloc_4662_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4661_;
            }
            19 => {
                if v_isShared_4667_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4666_, 0);
                    v___x_4669_ = v___x_4666_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
                    v___x_4669_ = v_reuseFailAlloc_4670_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4669_;
            }
            21 => {
                v___x_4676_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4676_, 0, v_a_4588_);
                leanh::lean_ctor_set(v___x_4676_, 1, v_a_4609_);
                leanh::lean_ctor_set(v___x_4676_, 2, v_a_4630_);
                leanh::lean_ctor_set(v___x_4676_, 3, v_a_4651_);
                leanh::lean_ctor_set(v___x_4676_, 4, v_a_4672_);
                if v_isShared_4675_ == 0 {
                    leanh::lean_ctor_set(v___x_4674_, 0, v___x_4676_);
                    v___x_4678_ = v___x_4674_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
                    v___x_4678_ = v_reuseFailAlloc_4679_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionParams_toJson(
    mut v_x_4683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toWorkDoneProgressParams_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPartialResultParams_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_textDocument_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_context_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toWorkDoneProgressParams_4684_ = leanh::lean_ctor_get(v_x_4683_, 0);
    leanh::lean_inc(v_toWorkDoneProgressParams_4684_);
    v_toPartialResultParams_4685_ = leanh::lean_ctor_get(v_x_4683_, 1);
    leanh::lean_inc(v_toPartialResultParams_4685_);
    v_textDocument_4686_ = leanh::lean_ctor_get(v_x_4683_, 2);
    leanh::lean_inc_ref(v_textDocument_4686_);
    v_range_4687_ = leanh::lean_ctor_get(v_x_4683_, 3);
    leanh::lean_inc_ref(v_range_4687_);
    v_context_4688_ = leanh::lean_ctor_get(v_x_4683_, 4);
    leanh::lean_inc_ref(v_context_4688_);
    leanh::lean_dec_ref(v_x_4683_);
    v___x_4689_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0;
    v___x_4690_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(v___x_4689_, v_toWorkDoneProgressParams_4684_);
    v___x_4691_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10;
    v___x_4692_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(v___x_4691_, v_toPartialResultParams_4685_);
    v___x_4693_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__16;
    v___x_4694_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_4686_);
    v___x_4695_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4695_, 0, v___x_4693_);
    leanh::lean_ctor_set(v___x_4695_, 1, v___x_4694_);
    v___x_4696_ = leanh::lean_box(0);
    v___x_4697_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4695_);
    leanh::lean_ctor_set(v___x_4697_, 1, v___x_4696_);
    v___x_4698_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__0;
    v___x_4699_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_4687_);
    v___x_4700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4700_, 0, v___x_4698_);
    leanh::lean_ctor_set(v___x_4700_, 1, v___x_4699_);
    v___x_4701_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4701_, 0, v___x_4700_);
    leanh::lean_ctor_set(v___x_4701_, 1, v___x_4696_);
    v___x_4702_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__23;
    v___x_4703_ = l_Lean_Lsp_instToJsonCodeActionContext_toJson(v_context_4688_);
    v___x_4704_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4704_, 0, v___x_4702_);
    leanh::lean_ctor_set(v___x_4704_, 1, v___x_4703_);
    v___x_4705_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4705_, 0, v___x_4704_);
    leanh::lean_ctor_set(v___x_4705_, 1, v___x_4696_);
    v___x_4706_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4706_, 0, v___x_4705_);
    leanh::lean_ctor_set(v___x_4706_, 1, v___x_4696_);
    v___x_4707_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4707_, 0, v___x_4701_);
    leanh::lean_ctor_set(v___x_4707_, 1, v___x_4706_);
    v___x_4708_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4708_, 0, v___x_4697_);
    leanh::lean_ctor_set(v___x_4708_, 1, v___x_4707_);
    v___x_4709_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4709_, 0, v___x_4692_);
    leanh::lean_ctor_set(v___x_4709_, 1, v___x_4708_);
    v___x_4710_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4710_, 0, v___x_4690_);
    leanh::lean_ctor_set(v___x_4710_, 1, v___x_4709_);
    v___x_4711_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_4712_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_4710_, v___x_4711_);
    v___x_4713_ = l_Lean_Json_mkObj(v___x_4712_);
    leanh::lean_dec(v___x_4712_);
    return v___x_4713_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4722_ = 1;
    v___x_4723_ = l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__2;
    v___x_4724_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4723_, v___x_4722_);
    return v___x_4724_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4725_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_4726_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__3,
    );
    v___x_4727_ = lean_string_append(v___x_4726_, v___x_4725_);
    return v___x_4727_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4730_: u8 = 0;
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4730_ = 1;
    v___x_4731_ = l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__5;
    v___x_4732_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4731_, v___x_4730_);
    return v___x_4732_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4733_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__6,
    );
    v___x_4734_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__4,
    );
    v___x_4735_ = lean_string_append(v___x_4734_, v___x_4733_);
    return v___x_4735_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4736_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4737_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__7,
    );
    v___x_4738_ = lean_string_append(v___x_4737_, v___x_4736_);
    return v___x_4738_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson(
    mut v_json_4739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v_a_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4755_: u8 = 0;
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v_a_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4763_: u8 = 0;
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4740_ = l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__0;
                v___x_4741_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__11(v_json_4739_, v___x_4740_);
                if leanh::lean_obj_tag(v___x_4741_) == 0 {
                    v_a_4742_ = leanh::lean_ctor_get(v___x_4741_, 0);
                    v_isSharedCheck_4751_ = (!leanh::lean_is_exclusive(v___x_4741_)) as u8;
                    if v_isSharedCheck_4751_ == 0 {
                        v___x_4744_ = v___x_4741_;
                        v_isShared_4745_ = v_isSharedCheck_4751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4742_);
                        leanh::lean_dec(v___x_4741_);
                        v___x_4744_ = leanh::lean_box(0);
                        v_isShared_4745_ = v_isSharedCheck_4751_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_4741_) == 0 {
                        v_a_4752_ = leanh::lean_ctor_get(v___x_4741_, 0);
                        v_isSharedCheck_4759_ =
                            (!leanh::lean_is_exclusive(v___x_4741_)) as u8;
                        if v_isSharedCheck_4759_ == 0 {
                            v___x_4754_ = v___x_4741_;
                            v_isShared_4755_ = v_isSharedCheck_4759_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4752_);
                            leanh::lean_dec(v___x_4741_);
                            v___x_4754_ = leanh::lean_box(0);
                            v_isShared_4755_ = v_isSharedCheck_4759_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4760_ = leanh::lean_ctor_get(v___x_4741_, 0);
                        v_isSharedCheck_4767_ =
                            (!leanh::lean_is_exclusive(v___x_4741_)) as u8;
                        if v_isSharedCheck_4767_ == 0 {
                            v___x_4762_ = v___x_4741_;
                            v_isShared_4763_ = v_isSharedCheck_4767_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4760_);
                            leanh::lean_dec(v___x_4741_);
                            v___x_4762_ = leanh::lean_box(0);
                            v_isShared_4763_ = v_isSharedCheck_4767_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4746_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__8,
                );
                v___x_4747_ = lean_string_append(v___x_4746_, v_a_4742_);
                leanh::lean_dec(v_a_4742_);
                if v_isShared_4745_ == 0 {
                    leanh::lean_ctor_set(v___x_4744_, 0, v___x_4747_);
                    v___x_4749_ = v___x_4744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
                    v___x_4749_ = v_reuseFailAlloc_4750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4749_;
            }
            3 => {
                if v_isShared_4755_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4754_, 0);
                    v___x_4757_ = v___x_4754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
                    v___x_4757_ = v_reuseFailAlloc_4758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4757_;
            }
            5 => {
                if v_isShared_4763_ == 0 {
                    v___x_4765_ = v___x_4762_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
                    v___x_4765_ = v_reuseFailAlloc_4766_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionDisabled_toJson(
    mut v_x_4770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4771_ = l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson___closed__0;
    v___x_4772_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4772_, 0, v_x_4770_);
    v___x_4773_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4773_, 0, v___x_4771_);
    leanh::lean_ctor_set(v___x_4773_, 1, v___x_4772_);
    v___x_4774_ = leanh::lean_box(0);
    v___x_4775_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4775_, 0, v___x_4773_);
    leanh::lean_ctor_set(v___x_4775_, 1, v___x_4774_);
    v___x_4776_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4776_, 0, v___x_4775_);
    leanh::lean_ctor_set(v___x_4776_, 1, v___x_4774_);
    v___x_4777_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_4778_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_4776_, v___x_4777_);
    v___x_4779_ = l_Lean_Json_mkObj(v___x_4778_);
    leanh::lean_dec(v___x_4778_);
    return v___x_4779_;
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionOptions_toJson(
    mut v_x_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toWorkDoneProgressOptions_4786_: u8 = 0;
    let mut v_codeActionKinds_x3f_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolveProvider_x3f_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toWorkDoneProgressOptions_4786_ = leanh::lean_ctor_get_uint8(
        v_x_4785_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_codeActionKinds_x3f_4787_ = leanh::lean_ctor_get(v_x_4785_, 0);
    leanh::lean_inc(v_codeActionKinds_x3f_4787_);
    v_resolveProvider_x3f_4788_ = leanh::lean_ctor_get(v_x_4785_, 1);
    leanh::lean_inc(v_resolveProvider_x3f_4788_);
    leanh::lean_dec_ref(v_x_4785_);
    v___x_4789_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__0;
    v___x_4790_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_4790_, 0 as u32, v_toWorkDoneProgressOptions_4786_);
    v___x_4791_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4791_, 0, v___x_4789_);
    leanh::lean_ctor_set(v___x_4791_, 1, v___x_4790_);
    v___x_4792_ = leanh::lean_box(0);
    v___x_4793_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4793_, 0, v___x_4791_);
    leanh::lean_ctor_set(v___x_4793_, 1, v___x_4792_);
    v___x_4794_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__1;
    v___x_4795_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1(
        v___x_4794_,
        v_codeActionKinds_x3f_4787_,
    );
    v___x_4796_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__2;
    v___x_4797_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_4796_, v_resolveProvider_x3f_4788_);
    leanh::lean_dec(v_resolveProvider_x3f_4788_);
    v___x_4798_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4798_, 0, v___x_4797_);
    leanh::lean_ctor_set(v___x_4798_, 1, v___x_4792_);
    v___x_4799_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4799_, 0, v___x_4795_);
    leanh::lean_ctor_set(v___x_4799_, 1, v___x_4798_);
    v___x_4800_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4800_, 0, v___x_4793_);
    leanh::lean_ctor_set(v___x_4800_, 1, v___x_4799_);
    v___x_4801_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_4802_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_4800_, v___x_4801_);
    v___x_4803_ = l_Lean_Json_mkObj(v___x_4802_);
    leanh::lean_dec(v___x_4802_);
    return v___x_4803_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionOptions_fromJson_spec__0(
    mut v_j_4806_: *mut leanh::LeanObject,
    mut v_k_4807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4808_ = l_Lean_Json_getObjValD(v_j_4806_, v_k_4807_);
    v___x_4809_ = l_Lean_Json_getBool_x3f(v___x_4808_);
    leanh::lean_dec(v___x_4808_);
    return v___x_4809_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionOptions_fromJson_spec__0___boxed(
    mut v_j_4810_: *mut leanh::LeanObject,
    mut v_k_4811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionOptions_fromJson_spec__0(v_j_4810_, v_k_4811_);
    leanh::lean_dec_ref(v_k_4811_);
    return v_res_4812_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = 1;
    v___x_4819_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__1;
    v___x_4820_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4819_, v___x_4818_);
    return v___x_4820_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4821_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_4822_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__2,
    );
    v___x_4823_ = lean_string_append(v___x_4822_, v___x_4821_);
    return v___x_4823_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4826_ = 1;
    v___x_4827_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__4;
    v___x_4828_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4827_, v___x_4826_);
    return v___x_4828_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4829_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__5,
    );
    v___x_4830_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3,
    );
    v___x_4831_ = lean_string_append(v___x_4830_, v___x_4829_);
    return v___x_4831_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__6,
    );
    v___x_4834_ = lean_string_append(v___x_4833_, v___x_4832_);
    return v___x_4834_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4838_: u8 = 0;
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = 1;
    v___x_4839_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__9;
    v___x_4840_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4839_, v___x_4838_);
    return v___x_4840_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__10,
    );
    v___x_4842_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3,
    );
    v___x_4843_ = lean_string_append(v___x_4842_, v___x_4841_);
    return v___x_4843_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4844_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__11,
    );
    v___x_4846_ = lean_string_append(v___x_4845_, v___x_4844_);
    return v___x_4846_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_4850_: u8 = 0;
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = 1;
    v___x_4851_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__14;
    v___x_4852_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4851_, v___x_4850_);
    return v___x_4852_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4853_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__15_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__15,
    );
    v___x_4854_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__3,
    );
    v___x_4855_ = lean_string_append(v___x_4854_, v___x_4853_);
    return v___x_4855_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4856_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_4857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__16,
    );
    v___x_4858_ = lean_string_append(v___x_4857_, v___x_4856_);
    return v___x_4858_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson(
    mut v_json_4859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4865_: u8 = 0;
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut v_a_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_a_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4886_: u8 = 0;
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut v_a_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4900_: u8 = 0;
    let mut v_a_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4907_: u8 = 0;
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_a_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4917_: u8 = 0;
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4921_: u8 = 0;
    let mut v_a_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4925_: u8 = 0;
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: u8 = 0;
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4860_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__0;
                leanh::lean_inc(v_json_4859_);
                v___x_4861_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionOptions_fromJson_spec__0(v_json_4859_, v___x_4860_);
                if leanh::lean_obj_tag(v___x_4861_) == 0 {
                    leanh::lean_dec(v_json_4859_);
                    v_a_4862_ = leanh::lean_ctor_get(v___x_4861_, 0);
                    v_isSharedCheck_4871_ = (!leanh::lean_is_exclusive(v___x_4861_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4864_ = v___x_4861_;
                        v_isShared_4865_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4862_);
                        leanh::lean_dec(v___x_4861_);
                        v___x_4864_ = leanh::lean_box(0);
                        v_isShared_4865_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_4861_) == 0 {
                        leanh::lean_dec(v_json_4859_);
                        v_a_4872_ = leanh::lean_ctor_get(v___x_4861_, 0);
                        v_isSharedCheck_4879_ =
                            (!leanh::lean_is_exclusive(v___x_4861_)) as u8;
                        if v_isSharedCheck_4879_ == 0 {
                            v___x_4874_ = v___x_4861_;
                            v_isShared_4875_ = v_isSharedCheck_4879_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4872_);
                            leanh::lean_dec(v___x_4861_);
                            v___x_4874_ = leanh::lean_box(0);
                            v_isShared_4875_ = v_isSharedCheck_4879_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4880_ = leanh::lean_ctor_get(v___x_4861_, 0);
                        leanh::lean_inc(v_a_4880_);
                        leanh::lean_dec_ref_known(v___x_4861_, 1);
                        v___x_4881_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__1;
                        leanh::lean_inc(v_json_4859_);
                        v___x_4882_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1(v_json_4859_, v___x_4881_);
                        if leanh::lean_obj_tag(v___x_4882_) == 0 {
                            leanh::lean_dec(v_a_4880_);
                            leanh::lean_dec(v_json_4859_);
                            v_a_4883_ = leanh::lean_ctor_get(v___x_4882_, 0);
                            v_isSharedCheck_4892_ =
                                (!leanh::lean_is_exclusive(v___x_4882_)) as u8;
                            if v_isSharedCheck_4892_ == 0 {
                                v___x_4885_ = v___x_4882_;
                                v_isShared_4886_ = v_isSharedCheck_4892_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4883_);
                                leanh::lean_dec(v___x_4882_);
                                v___x_4885_ = leanh::lean_box(0);
                                v_isShared_4886_ = v_isSharedCheck_4892_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_4882_) == 0 {
                                leanh::lean_dec(v_a_4880_);
                                leanh::lean_dec(v_json_4859_);
                                v_a_4893_ = leanh::lean_ctor_get(v___x_4882_, 0);
                                v_isSharedCheck_4900_ =
                                    (!leanh::lean_is_exclusive(v___x_4882_)) as u8;
                                if v_isSharedCheck_4900_ == 0 {
                                    v___x_4895_ = v___x_4882_;
                                    v_isShared_4896_ = v_isSharedCheck_4900_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4893_);
                                    leanh::lean_dec(v___x_4882_);
                                    v___x_4895_ = leanh::lean_box(0);
                                    v_isShared_4896_ = v_isSharedCheck_4900_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4901_ = leanh::lean_ctor_get(v___x_4882_, 0);
                                leanh::lean_inc(v_a_4901_);
                                leanh::lean_dec_ref_known(v___x_4882_, 1);
                                v___x_4902_ =
                                    l_Lean_Lsp_instToJsonCodeActionOptions_toJson___closed__2;
                                v___x_4903_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_4859_, v___x_4902_);
                                if leanh::lean_obj_tag(v___x_4903_) == 0 {
                                    leanh::lean_dec(v_a_4901_);
                                    leanh::lean_dec(v_a_4880_);
                                    v_a_4904_ = leanh::lean_ctor_get(v___x_4903_, 0);
                                    v_isSharedCheck_4913_ =
                                        (!leanh::lean_is_exclusive(v___x_4903_)) as u8;
                                    if v_isSharedCheck_4913_ == 0 {
                                        v___x_4906_ = v___x_4903_;
                                        v_isShared_4907_ = v_isSharedCheck_4913_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4904_);
                                        leanh::lean_dec(v___x_4903_);
                                        v___x_4906_ = leanh::lean_box(0);
                                        v_isShared_4907_ = v_isSharedCheck_4913_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_4903_) == 0 {
                                        leanh::lean_dec(v_a_4901_);
                                        leanh::lean_dec(v_a_4880_);
                                        v_a_4914_ = leanh::lean_ctor_get(v___x_4903_, 0);
                                        v_isSharedCheck_4921_ =
                                            (!leanh::lean_is_exclusive(v___x_4903_)) as u8;
                                        if v_isSharedCheck_4921_ == 0 {
                                            v___x_4916_ = v___x_4903_;
                                            v_isShared_4917_ = v_isSharedCheck_4921_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4914_);
                                            leanh::lean_dec(v___x_4903_);
                                            v___x_4916_ = leanh::lean_box(0);
                                            v_isShared_4917_ = v_isSharedCheck_4921_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4922_ = leanh::lean_ctor_get(v___x_4903_, 0);
                                        v_isSharedCheck_4931_ =
                                            (!leanh::lean_is_exclusive(v___x_4903_)) as u8;
                                        if v_isSharedCheck_4931_ == 0 {
                                            v___x_4924_ = v___x_4903_;
                                            v_isShared_4925_ = v_isSharedCheck_4931_;
                                            state = 13;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4922_);
                                            leanh::lean_dec(v___x_4903_);
                                            v___x_4924_ = leanh::lean_box(0);
                                            v_isShared_4925_ = v_isSharedCheck_4931_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4866_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__7,
                );
                v___x_4867_ = lean_string_append(v___x_4866_, v_a_4862_);
                leanh::lean_dec(v_a_4862_);
                if v_isShared_4865_ == 0 {
                    leanh::lean_ctor_set(v___x_4864_, 0, v___x_4867_);
                    v___x_4869_ = v___x_4864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4867_);
                    v___x_4869_ = v_reuseFailAlloc_4870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4869_;
            }
            3 => {
                if v_isShared_4875_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4874_, 0);
                    v___x_4877_ = v___x_4874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4877_;
            }
            5 => {
                v___x_4887_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__12,
                );
                v___x_4888_ = lean_string_append(v___x_4887_, v_a_4883_);
                leanh::lean_dec(v_a_4883_);
                if v_isShared_4886_ == 0 {
                    leanh::lean_ctor_set(v___x_4885_, 0, v___x_4888_);
                    v___x_4890_ = v___x_4885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
                    v___x_4890_ = v_reuseFailAlloc_4891_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4890_;
            }
            7 => {
                if v_isShared_4896_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4895_, 0);
                    v___x_4898_ = v___x_4895_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4899_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
                    v___x_4898_ = v_reuseFailAlloc_4899_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4898_;
            }
            9 => {
                v___x_4908_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__17_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson___closed__17,
                );
                v___x_4909_ = lean_string_append(v___x_4908_, v_a_4904_);
                leanh::lean_dec(v_a_4904_);
                if v_isShared_4907_ == 0 {
                    leanh::lean_ctor_set(v___x_4906_, 0, v___x_4909_);
                    v___x_4911_ = v___x_4906_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
                    v___x_4911_ = v_reuseFailAlloc_4912_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4911_;
            }
            11 => {
                if v_isShared_4917_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4916_, 0);
                    v___x_4919_ = v___x_4916_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
                    v___x_4919_ = v_reuseFailAlloc_4920_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4919_;
            }
            13 => {
                v___x_4926_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4926_, 0, v_a_4901_);
                leanh::lean_ctor_set(v___x_4926_, 1, v_a_4922_);
                v___x_4927_ = (leanh::lean_unbox(v_a_4880_) as u8);
                leanh::lean_dec(v_a_4880_);
                leanh::lean_ctor_set_uint8(
                    v___x_4926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4927_,
                );
                if v_isShared_4925_ == 0 {
                    leanh::lean_ctor_set(v___x_4924_, 0, v___x_4926_);
                    v___x_4929_ = v___x_4924_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4926_);
                    v___x_4929_ = v_reuseFailAlloc_4930_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__1(
    mut v_k_4934_: *mut leanh::LeanObject,
    mut v_x_4935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4935_) == 0 {
        let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4934_);
        v___x_4936_ = leanh::lean_box(0);
        return v___x_4936_;
    } else {
        let mut v_val_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4937_ = leanh::lean_ctor_get(v_x_4935_, 0);
        leanh::lean_inc(v_val_4937_);
        leanh::lean_dec_ref_known(v_x_4935_, 1);
        v___x_4938_ = l_Lean_Lsp_instToJsonCodeActionDisabled_toJson(v_val_4937_);
        v___x_4939_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4939_, 0, v_k_4934_);
        leanh::lean_ctor_set(v___x_4939_, 1, v___x_4938_);
        v___x_4940_ = leanh::lean_box(0);
        v___x_4941_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4941_, 0, v___x_4939_);
        leanh::lean_ctor_set(v___x_4941_, 1, v___x_4940_);
        return v___x_4941_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__2(
    mut v_k_4942_: *mut leanh::LeanObject,
    mut v_x_4943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4943_) == 0 {
        let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4942_);
        v___x_4944_ = leanh::lean_box(0);
        return v___x_4944_;
    } else {
        let mut v_val_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4945_ = leanh::lean_ctor_get(v_x_4943_, 0);
        leanh::lean_inc(v_val_4945_);
        leanh::lean_dec_ref_known(v_x_4943_, 1);
        v___x_4946_ = l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(v_val_4945_);
        v___x_4947_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4947_, 0, v_k_4942_);
        leanh::lean_ctor_set(v___x_4947_, 1, v___x_4946_);
        v___x_4948_ = leanh::lean_box(0);
        v___x_4949_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4949_, 0, v___x_4947_);
        leanh::lean_ctor_set(v___x_4949_, 1, v___x_4948_);
        return v___x_4949_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__3(
    mut v_k_4950_: *mut leanh::LeanObject,
    mut v_x_4951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4951_) == 0 {
        let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4950_);
        v___x_4952_ = leanh::lean_box(0);
        return v___x_4952_;
    } else {
        let mut v_val_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4953_ = leanh::lean_ctor_get(v_x_4951_, 0);
        leanh::lean_inc(v_val_4953_);
        leanh::lean_dec_ref_known(v_x_4951_, 1);
        v___x_4954_ = l_Lean_Lsp_instToJsonCommand_toJson(v_val_4953_);
        v___x_4955_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4955_, 0, v_k_4950_);
        leanh::lean_ctor_set(v___x_4955_, 1, v___x_4954_);
        v___x_4956_ = leanh::lean_box(0);
        v___x_4957_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4957_, 0, v___x_4955_);
        leanh::lean_ctor_set(v___x_4957_, 1, v___x_4956_);
        return v___x_4957_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__0(
    mut v_k_4958_: *mut leanh::LeanObject,
    mut v_x_4959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4959_) == 0 {
        let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4958_);
        v___x_4960_ = leanh::lean_box(0);
        return v___x_4960_;
    } else {
        let mut v_val_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4961_ = leanh::lean_ctor_get(v_x_4959_, 0);
        leanh::lean_inc(v_val_4961_);
        leanh::lean_dec_ref_known(v_x_4959_, 1);
        v___x_4962_ = l_Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0(
            v_val_4961_,
        );
        v___x_4963_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4963_, 0, v_k_4958_);
        leanh::lean_ctor_set(v___x_4963_, 1, v___x_4962_);
        v___x_4964_ = leanh::lean_box(0);
        v___x_4965_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4965_, 0, v___x_4963_);
        leanh::lean_ctor_set(v___x_4965_, 1, v___x_4964_);
        return v___x_4965_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeAction_toJson(
    mut v_x_4972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toWorkDoneProgressParams_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPartialResultParams_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_x3f_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreferred_x3f_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disabled_x3f_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_x3f_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_command_x3f_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toWorkDoneProgressParams_4973_ = leanh::lean_ctor_get(v_x_4972_, 0);
    leanh::lean_inc(v_toWorkDoneProgressParams_4973_);
    v_toPartialResultParams_4974_ = leanh::lean_ctor_get(v_x_4972_, 1);
    leanh::lean_inc(v_toPartialResultParams_4974_);
    v_title_4975_ = leanh::lean_ctor_get(v_x_4972_, 2);
    leanh::lean_inc_ref(v_title_4975_);
    v_kind_x3f_4976_ = leanh::lean_ctor_get(v_x_4972_, 3);
    leanh::lean_inc(v_kind_x3f_4976_);
    v_diagnostics_x3f_4977_ = leanh::lean_ctor_get(v_x_4972_, 4);
    leanh::lean_inc(v_diagnostics_x3f_4977_);
    v_isPreferred_x3f_4978_ = leanh::lean_ctor_get(v_x_4972_, 5);
    leanh::lean_inc(v_isPreferred_x3f_4978_);
    v_disabled_x3f_4979_ = leanh::lean_ctor_get(v_x_4972_, 6);
    leanh::lean_inc(v_disabled_x3f_4979_);
    v_edit_x3f_4980_ = leanh::lean_ctor_get(v_x_4972_, 7);
    leanh::lean_inc(v_edit_x3f_4980_);
    v_command_x3f_4981_ = leanh::lean_ctor_get(v_x_4972_, 8);
    leanh::lean_inc(v_command_x3f_4981_);
    v_data_x3f_4982_ = leanh::lean_ctor_get(v_x_4972_, 9);
    leanh::lean_inc(v_data_x3f_4982_);
    leanh::lean_dec_ref(v_x_4972_);
    v___x_4983_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0;
    v___x_4984_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(v___x_4983_, v_toWorkDoneProgressParams_4973_);
    v___x_4985_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10;
    v___x_4986_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(v___x_4985_, v_toPartialResultParams_4974_);
    v___x_4987_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__0;
    v___x_4988_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4988_, 0, v_title_4975_);
    v___x_4989_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4989_, 0, v___x_4987_);
    leanh::lean_ctor_set(v___x_4989_, 1, v___x_4988_);
    v___x_4990_ = leanh::lean_box(0);
    v___x_4991_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4991_, 0, v___x_4989_);
    leanh::lean_ctor_set(v___x_4991_, 1, v___x_4990_);
    v___x_4992_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__1;
    v___x_4993_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__6(v___x_4992_, v_kind_x3f_4976_);
    v___x_4994_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0;
    v___x_4995_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__0(
        v___x_4994_,
        v_diagnostics_x3f_4977_,
    );
    v___x_4996_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__2;
    v___x_4997_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_4996_, v_isPreferred_x3f_4978_);
    leanh::lean_dec(v_isPreferred_x3f_4978_);
    v___x_4998_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__3;
    v___x_4999_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__1(
        v___x_4998_,
        v_disabled_x3f_4979_,
    );
    v___x_5000_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__4;
    v___x_5001_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__2(
        v___x_5000_,
        v_edit_x3f_4980_,
    );
    v___x_5002_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__5;
    v___x_5003_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeAction_toJson_spec__3(
        v___x_5002_,
        v_command_x3f_4981_,
    );
    v___x_5004_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66;
    v___x_5005_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__10(v___x_5004_, v_data_x3f_4982_);
    leanh::lean_dec(v_data_x3f_4982_);
    v___x_5006_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5006_, 0, v___x_5005_);
    leanh::lean_ctor_set(v___x_5006_, 1, v___x_4990_);
    v___x_5007_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5007_, 0, v___x_5003_);
    leanh::lean_ctor_set(v___x_5007_, 1, v___x_5006_);
    v___x_5008_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5008_, 0, v___x_5001_);
    leanh::lean_ctor_set(v___x_5008_, 1, v___x_5007_);
    v___x_5009_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5009_, 0, v___x_4999_);
    leanh::lean_ctor_set(v___x_5009_, 1, v___x_5008_);
    v___x_5010_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5010_, 0, v___x_4997_);
    leanh::lean_ctor_set(v___x_5010_, 1, v___x_5009_);
    v___x_5011_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5011_, 0, v___x_4995_);
    leanh::lean_ctor_set(v___x_5011_, 1, v___x_5010_);
    v___x_5012_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5012_, 0, v___x_4993_);
    leanh::lean_ctor_set(v___x_5012_, 1, v___x_5011_);
    v___x_5013_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5013_, 0, v___x_4991_);
    leanh::lean_ctor_set(v___x_5013_, 1, v___x_5012_);
    v___x_5014_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5014_, 0, v___x_4986_);
    leanh::lean_ctor_set(v___x_5014_, 1, v___x_5013_);
    v___x_5015_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5015_, 0, v___x_4984_);
    leanh::lean_ctor_set(v___x_5015_, 1, v___x_5014_);
    v___x_5016_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_5017_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_5015_, v___x_5016_);
    v___x_5018_ = l_Lean_Json_mkObj(v___x_5017_);
    leanh::lean_dec(v___x_5017_);
    return v___x_5018_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3_spec__6(
    mut v_x_5023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5029_: u8 = 0;
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5033_: u8 = 0;
    let mut v_a_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5037_: u8 = 0;
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5023_) == 0 {
                    v___x_5024_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3_spec__6___closed__0;
                    return v___x_5024_;
                } else {
                    v___x_5025_ = l_Lean_Lsp_instFromJsonCommand_fromJson(v_x_5023_);
                    if leanh::lean_obj_tag(v___x_5025_) == 0 {
                        v_a_5026_ = leanh::lean_ctor_get(v___x_5025_, 0);
                        v_isSharedCheck_5033_ =
                            (!leanh::lean_is_exclusive(v___x_5025_)) as u8;
                        if v_isSharedCheck_5033_ == 0 {
                            v___x_5028_ = v___x_5025_;
                            v_isShared_5029_ = v_isSharedCheck_5033_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5026_);
                            leanh::lean_dec(v___x_5025_);
                            v___x_5028_ = leanh::lean_box(0);
                            v_isShared_5029_ = v_isSharedCheck_5033_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5034_ = leanh::lean_ctor_get(v___x_5025_, 0);
                        v_isSharedCheck_5042_ =
                            (!leanh::lean_is_exclusive(v___x_5025_)) as u8;
                        if v_isSharedCheck_5042_ == 0 {
                            v___x_5036_ = v___x_5025_;
                            v_isShared_5037_ = v_isSharedCheck_5042_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5034_);
                            leanh::lean_dec(v___x_5025_);
                            v___x_5036_ = leanh::lean_box(0);
                            v_isShared_5037_ = v_isSharedCheck_5042_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5029_ == 0 {
                    v___x_5031_ = v___x_5028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
                    v___x_5031_ = v_reuseFailAlloc_5032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5031_;
            }
            3 => {
                v___x_5038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5038_, 0, v_a_5034_);
                if v_isShared_5037_ == 0 {
                    leanh::lean_ctor_set(v___x_5036_, 0, v___x_5038_);
                    v___x_5040_ = v___x_5036_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_5038_);
                    v___x_5040_ = v_reuseFailAlloc_5041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3(
    mut v_j_5043_: *mut leanh::LeanObject,
    mut v_k_5044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5045_ = l_Lean_Json_getObjValD(v_j_5043_, v_k_5044_);
    v___x_5046_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3_spec__6(v___x_5045_);
    return v___x_5046_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3___boxed(
    mut v_j_5047_: *mut leanh::LeanObject,
    mut v_k_5048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5049_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3(
            v_j_5047_, v_k_5048_,
        );
    leanh::lean_dec_ref(v_k_5048_);
    return v_res_5049_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2_spec__4(
    mut v_x_5052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5058_: u8 = 0;
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5062_: u8 = 0;
    let mut v_a_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5066_: u8 = 0;
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5052_) == 0 {
                    v___x_5053_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2_spec__4___closed__0;
                    return v___x_5053_;
                } else {
                    v___x_5054_ = l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(v_x_5052_);
                    if leanh::lean_obj_tag(v___x_5054_) == 0 {
                        v_a_5055_ = leanh::lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5062_ =
                            (!leanh::lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5062_ == 0 {
                            v___x_5057_ = v___x_5054_;
                            v_isShared_5058_ = v_isSharedCheck_5062_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5055_);
                            leanh::lean_dec(v___x_5054_);
                            v___x_5057_ = leanh::lean_box(0);
                            v_isShared_5058_ = v_isSharedCheck_5062_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5063_ = leanh::lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5071_ =
                            (!leanh::lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5071_ == 0 {
                            v___x_5065_ = v___x_5054_;
                            v_isShared_5066_ = v_isSharedCheck_5071_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5063_);
                            leanh::lean_dec(v___x_5054_);
                            v___x_5065_ = leanh::lean_box(0);
                            v_isShared_5066_ = v_isSharedCheck_5071_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5058_ == 0 {
                    v___x_5060_ = v___x_5057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
                    v___x_5060_ = v_reuseFailAlloc_5061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5060_;
            }
            3 => {
                v___x_5067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5067_, 0, v_a_5063_);
                if v_isShared_5066_ == 0 {
                    leanh::lean_ctor_set(v___x_5065_, 0, v___x_5067_);
                    v___x_5069_ = v___x_5065_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
                    v___x_5069_ = v_reuseFailAlloc_5070_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2(
    mut v_j_5072_: *mut leanh::LeanObject,
    mut v_k_5073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5074_ = l_Lean_Json_getObjValD(v_j_5072_, v_k_5073_);
    v___x_5075_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2_spec__4(v___x_5074_);
    return v___x_5075_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2___boxed(
    mut v_j_5076_: *mut leanh::LeanObject,
    mut v_k_5077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5078_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2(
            v_j_5076_, v_k_5077_,
        );
    leanh::lean_dec_ref(v_k_5077_);
    return v_res_5078_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__1_spec__2(
    mut v_x_5079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut v_a_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5079_) == 0 {
                    v___x_5080_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10_spec__16___closed__0;
                    return v___x_5080_;
                } else {
                    v___x_5081_ = l_Lean_Lsp_instFromJsonCodeActionDisabled_fromJson(v_x_5079_);
                    if leanh::lean_obj_tag(v___x_5081_) == 0 {
                        v_a_5082_ = leanh::lean_ctor_get(v___x_5081_, 0);
                        v_isSharedCheck_5089_ =
                            (!leanh::lean_is_exclusive(v___x_5081_)) as u8;
                        if v_isSharedCheck_5089_ == 0 {
                            v___x_5084_ = v___x_5081_;
                            v_isShared_5085_ = v_isSharedCheck_5089_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5082_);
                            leanh::lean_dec(v___x_5081_);
                            v___x_5084_ = leanh::lean_box(0);
                            v_isShared_5085_ = v_isSharedCheck_5089_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5090_ = leanh::lean_ctor_get(v___x_5081_, 0);
                        v_isSharedCheck_5098_ =
                            (!leanh::lean_is_exclusive(v___x_5081_)) as u8;
                        if v_isSharedCheck_5098_ == 0 {
                            v___x_5092_ = v___x_5081_;
                            v_isShared_5093_ = v_isSharedCheck_5098_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5090_);
                            leanh::lean_dec(v___x_5081_);
                            v___x_5092_ = leanh::lean_box(0);
                            v_isShared_5093_ = v_isSharedCheck_5098_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5085_ == 0 {
                    v___x_5087_ = v___x_5084_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
                    v___x_5087_ = v_reuseFailAlloc_5088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5087_;
            }
            3 => {
                v___x_5094_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5094_, 0, v_a_5090_);
                if v_isShared_5093_ == 0 {
                    leanh::lean_ctor_set(v___x_5092_, 0, v___x_5094_);
                    v___x_5096_ = v___x_5092_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
                    v___x_5096_ = v_reuseFailAlloc_5097_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__1(
    mut v_j_5099_: *mut leanh::LeanObject,
    mut v_k_5100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5101_ = l_Lean_Json_getObjValD(v_j_5099_, v_k_5100_);
    v___x_5102_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__1_spec__2(v___x_5101_);
    return v___x_5102_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__1___boxed(
    mut v_j_5103_: *mut leanh::LeanObject,
    mut v_k_5104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5105_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__1(
            v_j_5103_, v_k_5104_,
        );
    leanh::lean_dec_ref(v_k_5104_);
    return v_res_5105_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0_spec__0(
    mut v_x_5108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5114_: u8 = 0;
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5118_: u8 = 0;
    let mut v_a_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5122_: u8 = 0;
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5108_) == 0 {
                    v___x_5109_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0_spec__0___closed__0;
                    return v___x_5109_;
                } else {
                    v___x_5110_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0(v_x_5108_);
                    if leanh::lean_obj_tag(v___x_5110_) == 0 {
                        v_a_5111_ = leanh::lean_ctor_get(v___x_5110_, 0);
                        v_isSharedCheck_5118_ =
                            (!leanh::lean_is_exclusive(v___x_5110_)) as u8;
                        if v_isSharedCheck_5118_ == 0 {
                            v___x_5113_ = v___x_5110_;
                            v_isShared_5114_ = v_isSharedCheck_5118_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5111_);
                            leanh::lean_dec(v___x_5110_);
                            v___x_5113_ = leanh::lean_box(0);
                            v_isShared_5114_ = v_isSharedCheck_5118_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5119_ = leanh::lean_ctor_get(v___x_5110_, 0);
                        v_isSharedCheck_5127_ =
                            (!leanh::lean_is_exclusive(v___x_5110_)) as u8;
                        if v_isSharedCheck_5127_ == 0 {
                            v___x_5121_ = v___x_5110_;
                            v_isShared_5122_ = v_isSharedCheck_5127_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5119_);
                            leanh::lean_dec(v___x_5110_);
                            v___x_5121_ = leanh::lean_box(0);
                            v_isShared_5122_ = v_isSharedCheck_5127_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5114_ == 0 {
                    v___x_5116_ = v___x_5113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
                    v___x_5116_ = v_reuseFailAlloc_5117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5116_;
            }
            3 => {
                v___x_5123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5123_, 0, v_a_5119_);
                if v_isShared_5122_ == 0 {
                    leanh::lean_ctor_set(v___x_5121_, 0, v___x_5123_);
                    v___x_5125_ = v___x_5121_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5126_, 0, v___x_5123_);
                    v___x_5125_ = v_reuseFailAlloc_5126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0(
    mut v_j_5128_: *mut leanh::LeanObject,
    mut v_k_5129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5130_ = l_Lean_Json_getObjValD(v_j_5128_, v_k_5129_);
    v___x_5131_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0_spec__0(v___x_5130_);
    return v___x_5131_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0___boxed(
    mut v_j_5132_: *mut leanh::LeanObject,
    mut v_k_5133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5134_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0(
            v_j_5132_, v_k_5133_,
        );
    leanh::lean_dec_ref(v_k_5133_);
    return v_res_5134_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5140_ = 1;
    v___x_5141_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__1;
    v___x_5142_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5141_, v___x_5140_);
    return v___x_5142_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5143_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_5144_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__2,
    );
    v___x_5145_ = lean_string_append(v___x_5144_, v___x_5143_);
    return v___x_5145_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5146_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__7,
    );
    v___x_5147_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5148_ = lean_string_append(v___x_5147_, v___x_5146_);
    return v___x_5148_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5149_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5150_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__4,
    );
    v___x_5151_ = lean_string_append(v___x_5150_, v___x_5149_);
    return v___x_5151_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5152_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__13,
    );
    v___x_5153_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5154_ = lean_string_append(v___x_5153_, v___x_5152_);
    return v___x_5154_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5155_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5156_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__6,
    );
    v___x_5157_ = lean_string_append(v___x_5156_, v___x_5155_);
    return v___x_5157_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5160_ = 1;
    v___x_5161_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__8;
    v___x_5162_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5161_, v___x_5160_);
    return v___x_5162_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__9,
    );
    v___x_5164_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5165_ = lean_string_append(v___x_5164_, v___x_5163_);
    return v___x_5165_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5166_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5167_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__10_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__10,
    );
    v___x_5168_ = lean_string_append(v___x_5167_, v___x_5166_);
    return v___x_5168_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_5172_: u8 = 0;
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5172_ = 1;
    v___x_5173_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__13;
    v___x_5174_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5173_, v___x_5172_);
    return v___x_5174_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__14,
    );
    v___x_5176_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5177_ = lean_string_append(v___x_5176_, v___x_5175_);
    return v___x_5177_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5178_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5179_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__15_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__15,
    );
    v___x_5180_ = lean_string_append(v___x_5179_, v___x_5178_);
    return v___x_5180_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5184_: u8 = 0;
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5184_ = 1;
    v___x_5185_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__18;
    v___x_5186_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5185_, v___x_5184_);
    return v___x_5186_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5187_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__19_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__19,
    );
    v___x_5188_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5189_ = lean_string_append(v___x_5188_, v___x_5187_);
    return v___x_5189_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5190_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5191_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__20_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__20,
    );
    v___x_5192_ = lean_string_append(v___x_5191_, v___x_5190_);
    return v___x_5192_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5196_ = 1;
    v___x_5197_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__23;
    v___x_5198_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5197_, v___x_5196_);
    return v___x_5198_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5199_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__24_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__24,
    );
    v___x_5200_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5201_ = lean_string_append(v___x_5200_, v___x_5199_);
    return v___x_5201_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5202_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5203_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__25_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__25,
    );
    v___x_5204_ = lean_string_append(v___x_5203_, v___x_5202_);
    return v___x_5204_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_5208_: u8 = 0;
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5208_ = 1;
    v___x_5209_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__28;
    v___x_5210_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5209_, v___x_5208_);
    return v___x_5210_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5211_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__29_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__29,
    );
    v___x_5212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5213_ = lean_string_append(v___x_5212_, v___x_5211_);
    return v___x_5213_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5214_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5215_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__30_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__30,
    );
    v___x_5216_ = lean_string_append(v___x_5215_, v___x_5214_);
    return v___x_5216_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_5220_: u8 = 0;
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5220_ = 1;
    v___x_5221_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__33;
    v___x_5222_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5221_, v___x_5220_);
    return v___x_5222_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__34_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__34,
    );
    v___x_5224_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5225_ = lean_string_append(v___x_5224_, v___x_5223_);
    return v___x_5225_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5227_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__35_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__35,
    );
    v___x_5228_ = lean_string_append(v___x_5227_, v___x_5226_);
    return v___x_5228_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5232_ = 1;
    v___x_5233_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__38;
    v___x_5234_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5233_, v___x_5232_);
    return v___x_5234_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__39_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__39,
    );
    v___x_5236_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__3,
    );
    v___x_5237_ = lean_string_append(v___x_5236_, v___x_5235_);
    return v___x_5237_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5238_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5239_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__40_once),
        _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__40,
    );
    v___x_5240_ = lean_string_append(v___x_5239_, v___x_5238_);
    return v___x_5240_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeAction_fromJson(
    mut v_json_5241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5247_: u8 = 0;
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v_a_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5257_: u8 = 0;
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5261_: u8 = 0;
    let mut v_a_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5268_: u8 = 0;
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_a_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5282_: u8 = 0;
    let mut v_a_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v_a_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5299_: u8 = 0;
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5303_: u8 = 0;
    let mut v_a_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5310_: u8 = 0;
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_a_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut v_a_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5331_: u8 = 0;
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5337_: u8 = 0;
    let mut v_a_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5341_: u8 = 0;
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5345_: u8 = 0;
    let mut v_a_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_a_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5362_: u8 = 0;
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5366_: u8 = 0;
    let mut v_a_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5379_: u8 = 0;
    let mut v_a_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5387_: u8 = 0;
    let mut v_a_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut v_a_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v_a_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5415_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5421_: u8 = 0;
    let mut v_a_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5425_: u8 = 0;
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5429_: u8 = 0;
    let mut v_a_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5242_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__0;
                leanh::lean_inc(v_json_5241_);
                v___x_5243_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_json_5241_, v___x_5242_);
                if leanh::lean_obj_tag(v___x_5243_) == 0 {
                    leanh::lean_dec(v_json_5241_);
                    v_a_5244_ = leanh::lean_ctor_get(v___x_5243_, 0);
                    v_isSharedCheck_5253_ = (!leanh::lean_is_exclusive(v___x_5243_)) as u8;
                    if v_isSharedCheck_5253_ == 0 {
                        v___x_5246_ = v___x_5243_;
                        v_isShared_5247_ = v_isSharedCheck_5253_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5244_);
                        leanh::lean_dec(v___x_5243_);
                        v___x_5246_ = leanh::lean_box(0);
                        v_isShared_5247_ = v_isSharedCheck_5253_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_5243_) == 0 {
                        leanh::lean_dec(v_json_5241_);
                        v_a_5254_ = leanh::lean_ctor_get(v___x_5243_, 0);
                        v_isSharedCheck_5261_ =
                            (!leanh::lean_is_exclusive(v___x_5243_)) as u8;
                        if v_isSharedCheck_5261_ == 0 {
                            v___x_5256_ = v___x_5243_;
                            v_isShared_5257_ = v_isSharedCheck_5261_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5254_);
                            leanh::lean_dec(v___x_5243_);
                            v___x_5256_ = leanh::lean_box(0);
                            v_isShared_5257_ = v_isSharedCheck_5261_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5262_ = leanh::lean_ctor_get(v___x_5243_, 0);
                        leanh::lean_inc(v_a_5262_);
                        leanh::lean_dec_ref_known(v___x_5243_, 1);
                        v___x_5263_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson___closed__10;
                        leanh::lean_inc(v_json_5241_);
                        v___x_5264_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_json_5241_, v___x_5263_);
                        if leanh::lean_obj_tag(v___x_5264_) == 0 {
                            leanh::lean_dec(v_a_5262_);
                            leanh::lean_dec(v_json_5241_);
                            v_a_5265_ = leanh::lean_ctor_get(v___x_5264_, 0);
                            v_isSharedCheck_5274_ =
                                (!leanh::lean_is_exclusive(v___x_5264_)) as u8;
                            if v_isSharedCheck_5274_ == 0 {
                                v___x_5267_ = v___x_5264_;
                                v_isShared_5268_ = v_isSharedCheck_5274_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5265_);
                                leanh::lean_dec(v___x_5264_);
                                v___x_5267_ = leanh::lean_box(0);
                                v_isShared_5268_ = v_isSharedCheck_5274_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_5264_) == 0 {
                                leanh::lean_dec(v_a_5262_);
                                leanh::lean_dec(v_json_5241_);
                                v_a_5275_ = leanh::lean_ctor_get(v___x_5264_, 0);
                                v_isSharedCheck_5282_ =
                                    (!leanh::lean_is_exclusive(v___x_5264_)) as u8;
                                if v_isSharedCheck_5282_ == 0 {
                                    v___x_5277_ = v___x_5264_;
                                    v_isShared_5278_ = v_isSharedCheck_5282_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5275_);
                                    leanh::lean_dec(v___x_5264_);
                                    v___x_5277_ = leanh::lean_box(0);
                                    v_isShared_5278_ = v_isSharedCheck_5282_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5283_ = leanh::lean_ctor_get(v___x_5264_, 0);
                                leanh::lean_inc(v_a_5283_);
                                leanh::lean_dec_ref_known(v___x_5264_, 1);
                                v___x_5284_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__0;
                                leanh::lean_inc(v_json_5241_);
                                v___x_5285_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__11(v_json_5241_, v___x_5284_);
                                if leanh::lean_obj_tag(v___x_5285_) == 0 {
                                    leanh::lean_dec(v_a_5283_);
                                    leanh::lean_dec(v_a_5262_);
                                    leanh::lean_dec(v_json_5241_);
                                    v_a_5286_ = leanh::lean_ctor_get(v___x_5285_, 0);
                                    v_isSharedCheck_5295_ =
                                        (!leanh::lean_is_exclusive(v___x_5285_)) as u8;
                                    if v_isSharedCheck_5295_ == 0 {
                                        v___x_5288_ = v___x_5285_;
                                        v_isShared_5289_ = v_isSharedCheck_5295_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5286_);
                                        leanh::lean_dec(v___x_5285_);
                                        v___x_5288_ = leanh::lean_box(0);
                                        v_isShared_5289_ = v_isSharedCheck_5295_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_5285_) == 0 {
                                        leanh::lean_dec(v_a_5283_);
                                        leanh::lean_dec(v_a_5262_);
                                        leanh::lean_dec(v_json_5241_);
                                        v_a_5296_ = leanh::lean_ctor_get(v___x_5285_, 0);
                                        v_isSharedCheck_5303_ =
                                            (!leanh::lean_is_exclusive(v___x_5285_)) as u8;
                                        if v_isSharedCheck_5303_ == 0 {
                                            v___x_5298_ = v___x_5285_;
                                            v_isShared_5299_ = v_isSharedCheck_5303_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5296_);
                                            leanh::lean_dec(v___x_5285_);
                                            v___x_5298_ = leanh::lean_box(0);
                                            v_isShared_5299_ = v_isSharedCheck_5303_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5304_ = leanh::lean_ctor_get(v___x_5285_, 0);
                                        leanh::lean_inc(v_a_5304_);
                                        leanh::lean_dec_ref_known(v___x_5285_, 1);
                                        v___x_5305_ =
                                            l_Lean_Lsp_instToJsonCodeAction_toJson___closed__1;
                                        leanh::lean_inc(v_json_5241_);
                                        v___x_5306_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__10(v_json_5241_, v___x_5305_);
                                        if leanh::lean_obj_tag(v___x_5306_) == 0 {
                                            leanh::lean_dec(v_a_5304_);
                                            leanh::lean_dec(v_a_5283_);
                                            leanh::lean_dec(v_a_5262_);
                                            leanh::lean_dec(v_json_5241_);
                                            v_a_5307_ = leanh::lean_ctor_get(v___x_5306_, 0);
                                            v_isSharedCheck_5316_ =
                                                (!leanh::lean_is_exclusive(v___x_5306_))
                                                    as u8;
                                            if v_isSharedCheck_5316_ == 0 {
                                                v___x_5309_ = v___x_5306_;
                                                v_isShared_5310_ = v_isSharedCheck_5316_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_5307_);
                                                leanh::lean_dec(v___x_5306_);
                                                v___x_5309_ = leanh::lean_box(0);
                                                v_isShared_5310_ = v_isSharedCheck_5316_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_5306_) == 0 {
                                                leanh::lean_dec(v_a_5304_);
                                                leanh::lean_dec(v_a_5283_);
                                                leanh::lean_dec(v_a_5262_);
                                                leanh::lean_dec(v_json_5241_);
                                                v_a_5317_ =
                                                    leanh::lean_ctor_get(v___x_5306_, 0);
                                                v_isSharedCheck_5324_ =
                                                    (!leanh::lean_is_exclusive(v___x_5306_))
                                                        as u8;
                                                if v_isSharedCheck_5324_ == 0 {
                                                    v___x_5319_ = v___x_5306_;
                                                    v_isShared_5320_ = v_isSharedCheck_5324_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5317_);
                                                    leanh::lean_dec(v___x_5306_);
                                                    v___x_5319_ = leanh::lean_box(0);
                                                    v_isShared_5320_ = v_isSharedCheck_5324_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5325_ =
                                                    leanh::lean_ctor_get(v___x_5306_, 0);
                                                leanh::lean_inc(v_a_5325_);
                                                leanh::lean_dec_ref_known(v___x_5306_, 1);
                                                v___x_5326_ = l_Lean_Lsp_instFromJsonCodeActionContext_fromJson___closed__0;
                                                leanh::lean_inc(v_json_5241_);
                                                v___x_5327_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__0(v_json_5241_, v___x_5326_);
                                                if leanh::lean_obj_tag(v___x_5327_) == 0 {
                                                    leanh::lean_dec(v_a_5325_);
                                                    leanh::lean_dec(v_a_5304_);
                                                    leanh::lean_dec(v_a_5283_);
                                                    leanh::lean_dec(v_a_5262_);
                                                    leanh::lean_dec(v_json_5241_);
                                                    v_a_5328_ =
                                                        leanh::lean_ctor_get(v___x_5327_, 0);
                                                    v_isSharedCheck_5337_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_5327_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5337_ == 0 {
                                                        v___x_5330_ = v___x_5327_;
                                                        v_isShared_5331_ = v_isSharedCheck_5337_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_5328_);
                                                        leanh::lean_dec(v___x_5327_);
                                                        v___x_5330_ = leanh::lean_box(0);
                                                        v_isShared_5331_ = v_isSharedCheck_5337_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_5327_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_5325_);
                                                        leanh::lean_dec(v_a_5304_);
                                                        leanh::lean_dec(v_a_5283_);
                                                        leanh::lean_dec(v_a_5262_);
                                                        leanh::lean_dec(v_json_5241_);
                                                        v_a_5338_ = leanh::lean_ctor_get(
                                                            v___x_5327_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5345_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_5327_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5345_ == 0 {
                                                            v___x_5340_ = v___x_5327_;
                                                            v_isShared_5341_ =
                                                                v_isSharedCheck_5345_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_5338_);
                                                            leanh::lean_dec(v___x_5327_);
                                                            v___x_5340_ = leanh::lean_box(0);
                                                            v_isShared_5341_ =
                                                                v_isSharedCheck_5345_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_5346_ = leanh::lean_ctor_get(
                                                            v___x_5327_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_5346_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_5327_,
                                                            1,
                                                        );
                                                        v___x_5347_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__2;
                                                        leanh::lean_inc(v_json_5241_);
                                                        v___x_5348_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_5241_, v___x_5347_);
                                                        if leanh::lean_obj_tag(v___x_5348_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_5346_);
                                                            leanh::lean_dec(v_a_5325_);
                                                            leanh::lean_dec(v_a_5304_);
                                                            leanh::lean_dec(v_a_5283_);
                                                            leanh::lean_dec(v_a_5262_);
                                                            leanh::lean_dec(v_json_5241_);
                                                            v_a_5349_ = leanh::lean_ctor_get(
                                                                v___x_5348_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5358_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_5348_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5358_ == 0 {
                                                                v___x_5351_ = v___x_5348_;
                                                                v_isShared_5352_ =
                                                                    v_isSharedCheck_5358_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_5349_);
                                                                leanh::lean_dec(v___x_5348_);
                                                                v___x_5351_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5352_ =
                                                                    v_isSharedCheck_5358_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v___x_5348_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec(v_a_5346_);
                                                                leanh::lean_dec(v_a_5325_);
                                                                leanh::lean_dec(v_a_5304_);
                                                                leanh::lean_dec(v_a_5283_);
                                                                leanh::lean_dec(v_a_5262_);
                                                                leanh::lean_dec(
                                                                    v_json_5241_,
                                                                );
                                                                v_a_5359_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5348_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5366_ = (!leanh::lean_is_exclusive(v___x_5348_)) as u8;
                                                                if v_isSharedCheck_5366_ == 0 {
                                                                    v___x_5361_ = v___x_5348_;
                                                                    v_isShared_5362_ =
                                                                        v_isSharedCheck_5366_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_5359_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_5348_,
                                                                    );
                                                                    v___x_5361_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_5362_ =
                                                                        v_isSharedCheck_5366_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_5367_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5348_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_5367_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_5348_,
                                                                    1,
                                                                );
                                                                v___x_5368_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__3;
                                                                leanh::lean_inc(
                                                                    v_json_5241_,
                                                                );
                                                                v___x_5369_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__1(v_json_5241_, v___x_5368_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_5369_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec(
                                                                        v_a_5367_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5346_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5325_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5304_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5283_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5262_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_json_5241_,
                                                                    );
                                                                    v_a_5370_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_5369_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5379_ = (!leanh::lean_is_exclusive(v___x_5369_)) as u8;
                                                                    if v_isSharedCheck_5379_ == 0 {
                                                                        v___x_5372_ = v___x_5369_;
                                                                        v_isShared_5373_ =
                                                                            v_isSharedCheck_5379_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_5370_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_5369_,
                                                                        );
                                                                        v___x_5372_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5373_ =
                                                                            v_isSharedCheck_5379_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_5369_,
                                                                    ) == 0
                                                                    {
                                                                        leanh::lean_dec(
                                                                            v_a_5367_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5346_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5325_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5304_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5283_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5262_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_json_5241_,
                                                                        );
                                                                        v_a_5380_ = leanh::lean_ctor_get(v___x_5369_, 0);
                                                                        v_isSharedCheck_5387_ = (!leanh::lean_is_exclusive(v___x_5369_)) as u8;
                                                                        if v_isSharedCheck_5387_
                                                                            == 0
                                                                        {
                                                                            v___x_5382_ =
                                                                                v___x_5369_;
                                                                            v_isShared_5383_ = v_isSharedCheck_5387_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_5380_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_5369_,
                                                                            );
                                                                            v___x_5382_ = leanh::lean_box(0);
                                                                            v_isShared_5383_ = v_isSharedCheck_5387_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_5388_ = leanh::lean_ctor_get(v___x_5369_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_5388_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_5369_, 1);
                                                                        v___x_5389_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__4;
                                                                        leanh::lean_inc(
                                                                            v_json_5241_,
                                                                        );
                                                                        v___x_5390_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__2(v_json_5241_, v___x_5389_);
                                                                        if leanh::lean_obj_tag(v___x_5390_) == 0 {
leanh::lean_dec(v_a_5388_);
leanh::lean_dec(v_a_5367_);
leanh::lean_dec(v_a_5346_);
leanh::lean_dec(v_a_5325_);
leanh::lean_dec(v_a_5304_);
leanh::lean_dec(v_a_5283_);
leanh::lean_dec(v_a_5262_);
leanh::lean_dec(v_json_5241_);
v_a_5391_ = leanh::lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5400_ = (!leanh::lean_is_exclusive(v___x_5390_)) as u8;
if v_isSharedCheck_5400_ == 0 {
v___x_5393_ = v___x_5390_;
v_isShared_5394_ = v_isSharedCheck_5400_;
state = 29; continue;
} else {
leanh::lean_inc(v_a_5391_);
leanh::lean_dec(v___x_5390_);
v___x_5393_ = leanh::lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5400_;
state = 29; continue;
}
} else {
if leanh::lean_obj_tag(v___x_5390_) == 0 {
leanh::lean_dec(v_a_5388_);
leanh::lean_dec(v_a_5367_);
leanh::lean_dec(v_a_5346_);
leanh::lean_dec(v_a_5325_);
leanh::lean_dec(v_a_5304_);
leanh::lean_dec(v_a_5283_);
leanh::lean_dec(v_a_5262_);
leanh::lean_dec(v_json_5241_);
v_a_5401_ = leanh::lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5408_ = (!leanh::lean_is_exclusive(v___x_5390_)) as u8;
if v_isSharedCheck_5408_ == 0 {
v___x_5403_ = v___x_5390_;
v_isShared_5404_ = v_isSharedCheck_5408_;
state = 31; continue;
} else {
leanh::lean_inc(v_a_5401_);
leanh::lean_dec(v___x_5390_);
v___x_5403_ = leanh::lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
state = 31; continue;
}
} else {
v_a_5409_ = leanh::lean_ctor_get(v___x_5390_, 0);
leanh::lean_inc(v_a_5409_);
leanh::lean_dec_ref_known(v___x_5390_, 1);
v___x_5410_ = l_Lean_Lsp_instToJsonCodeAction_toJson___closed__5;
leanh::lean_inc(v_json_5241_);
v___x_5411_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeAction_fromJson_spec__3(v_json_5241_, v___x_5410_);
if leanh::lean_obj_tag(v___x_5411_) == 0 {
leanh::lean_dec(v_a_5409_);
leanh::lean_dec(v_a_5388_);
leanh::lean_dec(v_a_5367_);
leanh::lean_dec(v_a_5346_);
leanh::lean_dec(v_a_5325_);
leanh::lean_dec(v_a_5304_);
leanh::lean_dec(v_a_5283_);
leanh::lean_dec(v_a_5262_);
leanh::lean_dec(v_json_5241_);
v_a_5412_ = leanh::lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5421_ = (!leanh::lean_is_exclusive(v___x_5411_)) as u8;
if v_isSharedCheck_5421_ == 0 {
v___x_5414_ = v___x_5411_;
v_isShared_5415_ = v_isSharedCheck_5421_;
state = 33; continue;
} else {
leanh::lean_inc(v_a_5412_);
leanh::lean_dec(v___x_5411_);
v___x_5414_ = leanh::lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5421_;
state = 33; continue;
}
} else {
if leanh::lean_obj_tag(v___x_5411_) == 0 {
leanh::lean_dec(v_a_5409_);
leanh::lean_dec(v_a_5388_);
leanh::lean_dec(v_a_5367_);
leanh::lean_dec(v_a_5346_);
leanh::lean_dec(v_a_5325_);
leanh::lean_dec(v_a_5304_);
leanh::lean_dec(v_a_5283_);
leanh::lean_dec(v_a_5262_);
leanh::lean_dec(v_json_5241_);
v_a_5422_ = leanh::lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5429_ = (!leanh::lean_is_exclusive(v___x_5411_)) as u8;
if v_isSharedCheck_5429_ == 0 {
v___x_5424_ = v___x_5411_;
v_isShared_5425_ = v_isSharedCheck_5429_;
state = 35; continue;
} else {
leanh::lean_inc(v_a_5422_);
leanh::lean_dec(v___x_5411_);
v___x_5424_ = leanh::lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5429_;
state = 35; continue;
}
} else {
v_a_5430_ = leanh::lean_ctor_get(v___x_5411_, 0);
leanh::lean_inc(v_a_5430_);
leanh::lean_dec_ref_known(v___x_5411_, 1);
v___x_5431_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__66;
v___x_5432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__15(v_json_5241_, v___x_5431_);
v_a_5433_ = leanh::lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5441_ = (!leanh::lean_is_exclusive(v___x_5432_)) as u8;
if v_isSharedCheck_5441_ == 0 {
v___x_5435_ = v___x_5432_;
v_isShared_5436_ = v_isSharedCheck_5441_;
state = 37; continue;
} else {
leanh::lean_inc(v_a_5433_);
leanh::lean_dec(v___x_5432_);
v___x_5435_ = leanh::lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5441_;
state = 37; continue;
}
}
}
}
}
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5248_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__5,
                );
                v___x_5249_ = lean_string_append(v___x_5248_, v_a_5244_);
                leanh::lean_dec(v_a_5244_);
                if v_isShared_5247_ == 0 {
                    leanh::lean_ctor_set(v___x_5246_, 0, v___x_5249_);
                    v___x_5251_ = v___x_5246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
                    v___x_5251_ = v_reuseFailAlloc_5252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5251_;
            }
            3 => {
                if v_isShared_5257_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5256_, 0);
                    v___x_5259_ = v___x_5256_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
                    v___x_5259_ = v_reuseFailAlloc_5260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5259_;
            }
            5 => {
                v___x_5269_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__7,
                );
                v___x_5270_ = lean_string_append(v___x_5269_, v_a_5265_);
                leanh::lean_dec(v_a_5265_);
                if v_isShared_5268_ == 0 {
                    leanh::lean_ctor_set(v___x_5267_, 0, v___x_5270_);
                    v___x_5272_ = v___x_5267_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5273_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
                    v___x_5272_ = v_reuseFailAlloc_5273_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5272_;
            }
            7 => {
                if v_isShared_5278_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5277_, 0);
                    v___x_5280_ = v___x_5277_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
                    v___x_5280_ = v_reuseFailAlloc_5281_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5280_;
            }
            9 => {
                v___x_5290_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__11,
                );
                v___x_5291_ = lean_string_append(v___x_5290_, v_a_5286_);
                leanh::lean_dec(v_a_5286_);
                if v_isShared_5289_ == 0 {
                    leanh::lean_ctor_set(v___x_5288_, 0, v___x_5291_);
                    v___x_5293_ = v___x_5288_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 0, v___x_5291_);
                    v___x_5293_ = v_reuseFailAlloc_5294_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5293_;
            }
            11 => {
                if v_isShared_5299_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5298_, 0);
                    v___x_5301_ = v___x_5298_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
                    v___x_5301_ = v_reuseFailAlloc_5302_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5301_;
            }
            13 => {
                v___x_5311_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__16
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__16_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__16,
                );
                v___x_5312_ = lean_string_append(v___x_5311_, v_a_5307_);
                leanh::lean_dec(v_a_5307_);
                if v_isShared_5310_ == 0 {
                    leanh::lean_ctor_set(v___x_5309_, 0, v___x_5312_);
                    v___x_5314_ = v___x_5309_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5312_);
                    v___x_5314_ = v_reuseFailAlloc_5315_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5314_;
            }
            15 => {
                if v_isShared_5320_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5319_, 0);
                    v___x_5322_ = v___x_5319_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5323_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5317_);
                    v___x_5322_ = v_reuseFailAlloc_5323_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5322_;
            }
            17 => {
                v___x_5332_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__21_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__21,
                );
                v___x_5333_ = lean_string_append(v___x_5332_, v_a_5328_);
                leanh::lean_dec(v_a_5328_);
                if v_isShared_5331_ == 0 {
                    leanh::lean_ctor_set(v___x_5330_, 0, v___x_5333_);
                    v___x_5335_ = v___x_5330_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5333_);
                    v___x_5335_ = v_reuseFailAlloc_5336_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5335_;
            }
            19 => {
                if v_isShared_5341_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5340_, 0);
                    v___x_5343_ = v___x_5340_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5338_);
                    v___x_5343_ = v_reuseFailAlloc_5344_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5343_;
            }
            21 => {
                v___x_5353_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__26
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__26_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__26,
                );
                v___x_5354_ = lean_string_append(v___x_5353_, v_a_5349_);
                leanh::lean_dec(v_a_5349_);
                if v_isShared_5352_ == 0 {
                    leanh::lean_ctor_set(v___x_5351_, 0, v___x_5354_);
                    v___x_5356_ = v___x_5351_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5354_);
                    v___x_5356_ = v_reuseFailAlloc_5357_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5356_;
            }
            23 => {
                if v_isShared_5362_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5361_, 0);
                    v___x_5364_ = v___x_5361_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5359_);
                    v___x_5364_ = v_reuseFailAlloc_5365_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5364_;
            }
            25 => {
                v___x_5374_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__31_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__31,
                );
                v___x_5375_ = lean_string_append(v___x_5374_, v_a_5370_);
                leanh::lean_dec(v_a_5370_);
                if v_isShared_5373_ == 0 {
                    leanh::lean_ctor_set(v___x_5372_, 0, v___x_5375_);
                    v___x_5377_ = v___x_5372_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
                    v___x_5377_ = v_reuseFailAlloc_5378_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5377_;
            }
            27 => {
                if v_isShared_5383_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5382_, 0);
                    v___x_5385_ = v___x_5382_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
                    v___x_5385_ = v_reuseFailAlloc_5386_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5385_;
            }
            29 => {
                v___x_5395_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__36
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__36_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__36,
                );
                v___x_5396_ = lean_string_append(v___x_5395_, v_a_5391_);
                leanh::lean_dec(v_a_5391_);
                if v_isShared_5394_ == 0 {
                    leanh::lean_ctor_set(v___x_5393_, 0, v___x_5396_);
                    v___x_5398_ = v___x_5393_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 0, v___x_5396_);
                    v___x_5398_ = v_reuseFailAlloc_5399_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5398_;
            }
            31 => {
                if v_isShared_5404_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5403_, 0);
                    v___x_5406_ = v___x_5403_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5406_;
            }
            33 => {
                v___x_5416_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__41
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__41_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeAction_fromJson___closed__41,
                );
                v___x_5417_ = lean_string_append(v___x_5416_, v_a_5412_);
                leanh::lean_dec(v_a_5412_);
                if v_isShared_5415_ == 0 {
                    leanh::lean_ctor_set(v___x_5414_, 0, v___x_5417_);
                    v___x_5419_ = v___x_5414_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5420_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5417_);
                    v___x_5419_ = v_reuseFailAlloc_5420_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5419_;
            }
            35 => {
                if v_isShared_5425_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5424_, 0);
                    v___x_5427_ = v___x_5424_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5422_);
                    v___x_5427_ = v_reuseFailAlloc_5428_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5427_;
            }
            37 => {
                v___x_5437_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                leanh::lean_ctor_set(v___x_5437_, 0, v_a_5262_);
                leanh::lean_ctor_set(v___x_5437_, 1, v_a_5283_);
                leanh::lean_ctor_set(v___x_5437_, 2, v_a_5304_);
                leanh::lean_ctor_set(v___x_5437_, 3, v_a_5325_);
                leanh::lean_ctor_set(v___x_5437_, 4, v_a_5346_);
                leanh::lean_ctor_set(v___x_5437_, 5, v_a_5367_);
                leanh::lean_ctor_set(v___x_5437_, 6, v_a_5388_);
                leanh::lean_ctor_set(v___x_5437_, 7, v_a_5409_);
                leanh::lean_ctor_set(v___x_5437_, 8, v_a_5430_);
                leanh::lean_ctor_set(v___x_5437_, 9, v_a_5433_);
                if v_isShared_5436_ == 0 {
                    leanh::lean_ctor_set(v___x_5435_, 0, v___x_5437_);
                    v___x_5439_ = v___x_5435_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5440_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5437_);
                    v___x_5439_ = v_reuseFailAlloc_5440_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson_spec__0(
    mut v_j_5444_: *mut leanh::LeanObject,
    mut v_k_5445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5446_ = l_Lean_Json_getObjValD(v_j_5444_, v_k_5445_);
    v___x_5447_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2_spec__5(v___x_5446_);
    return v___x_5447_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson_spec__0___boxed(
    mut v_j_5448_: *mut leanh::LeanObject,
    mut v_k_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5450_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson_spec__0(v_j_5448_, v_k_5449_);
    leanh::lean_dec_ref(v_k_5449_);
    return v_res_5450_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5457_: u8 = 0;
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5457_ = 1;
    v___x_5458_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__2;
    v___x_5459_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5458_, v___x_5457_);
    return v___x_5459_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5460_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_5461_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__3,
    );
    v___x_5462_ = lean_string_append(v___x_5461_, v___x_5460_);
    return v___x_5462_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5465_: u8 = 0;
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5465_ = 1;
    v___x_5466_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__5;
    v___x_5467_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5466_, v___x_5465_);
    return v___x_5467_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5468_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__6,
    );
    v___x_5469_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__4,
    );
    v___x_5470_ = lean_string_append(v___x_5469_, v___x_5468_);
    return v___x_5470_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5471_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5472_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__7,
    );
    v___x_5473_ = lean_string_append(v___x_5472_, v___x_5471_);
    return v___x_5473_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson(
    mut v_json_5474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5480_: u8 = 0;
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5486_: u8 = 0;
    let mut v_a_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_a_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5475_ =
                    l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__0;
                v___x_5476_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson_spec__0(v_json_5474_, v___x_5475_);
                if leanh::lean_obj_tag(v___x_5476_) == 0 {
                    v_a_5477_ = leanh::lean_ctor_get(v___x_5476_, 0);
                    v_isSharedCheck_5486_ = (!leanh::lean_is_exclusive(v___x_5476_)) as u8;
                    if v_isSharedCheck_5486_ == 0 {
                        v___x_5479_ = v___x_5476_;
                        v_isShared_5480_ = v_isSharedCheck_5486_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5477_);
                        leanh::lean_dec(v___x_5476_);
                        v___x_5479_ = leanh::lean_box(0);
                        v_isShared_5480_ = v_isSharedCheck_5486_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_5476_) == 0 {
                        v_a_5487_ = leanh::lean_ctor_get(v___x_5476_, 0);
                        v_isSharedCheck_5494_ =
                            (!leanh::lean_is_exclusive(v___x_5476_)) as u8;
                        if v_isSharedCheck_5494_ == 0 {
                            v___x_5489_ = v___x_5476_;
                            v_isShared_5490_ = v_isSharedCheck_5494_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5487_);
                            leanh::lean_dec(v___x_5476_);
                            v___x_5489_ = leanh::lean_box(0);
                            v_isShared_5490_ = v_isSharedCheck_5494_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5495_ = leanh::lean_ctor_get(v___x_5476_, 0);
                        v_isSharedCheck_5502_ =
                            (!leanh::lean_is_exclusive(v___x_5476_)) as u8;
                        if v_isSharedCheck_5502_ == 0 {
                            v___x_5497_ = v___x_5476_;
                            v_isShared_5498_ = v_isSharedCheck_5502_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5495_);
                            leanh::lean_dec(v___x_5476_);
                            v___x_5497_ = leanh::lean_box(0);
                            v_isShared_5498_ = v_isSharedCheck_5502_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__8);
                v___x_5482_ = lean_string_append(v___x_5481_, v_a_5477_);
                leanh::lean_dec(v_a_5477_);
                if v_isShared_5480_ == 0 {
                    leanh::lean_ctor_set(v___x_5479_, 0, v___x_5482_);
                    v___x_5484_ = v___x_5479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5485_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5482_);
                    v___x_5484_ = v_reuseFailAlloc_5485_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5484_;
            }
            3 => {
                if v_isShared_5490_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5489_, 0);
                    v___x_5492_ = v___x_5489_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
                    v___x_5492_ = v_reuseFailAlloc_5493_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5492_;
            }
            5 => {
                if v_isShared_5498_ == 0 {
                    v___x_5500_ = v___x_5497_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet_toJson(
    mut v_x_5505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5506_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson___closed__0;
    v___x_5507_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__1_spec__3(v_x_5505_);
    v___x_5508_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5508_, 0, v___x_5506_);
    leanh::lean_ctor_set(v___x_5508_, 1, v___x_5507_);
    v___x_5509_ = leanh::lean_box(0);
    v___x_5510_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5510_, 0, v___x_5508_);
    leanh::lean_ctor_set(v___x_5510_, 1, v___x_5509_);
    v___x_5511_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5511_, 0, v___x_5510_);
    leanh::lean_ctor_set(v___x_5511_, 1, v___x_5509_);
    v___x_5512_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_5513_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_5511_, v___x_5512_);
    v___x_5514_ = l_Lean_Json_mkObj(v___x_5513_);
    leanh::lean_dec(v___x_5513_);
    return v___x_5514_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson_spec__0(
    mut v_j_5517_: *mut leanh::LeanObject,
    mut v_k_5518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5519_ = l_Lean_Json_getObjValD(v_j_5517_, v_k_5518_);
    v___x_5520_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupportValueSet_fromJson(v___x_5519_);
    return v___x_5520_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson_spec__0___boxed(
    mut v_j_5521_: *mut leanh::LeanObject,
    mut v_k_5522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson_spec__0(v_j_5521_, v_k_5522_);
    leanh::lean_dec_ref(v_k_5522_);
    return v_res_5523_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5530_: u8 = 0;
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5530_ = 1;
    v___x_5531_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__2;
    v___x_5532_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5531_, v___x_5530_);
    return v___x_5532_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5533_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_5534_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__3,
    );
    v___x_5535_ = lean_string_append(v___x_5534_, v___x_5533_);
    return v___x_5535_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5538_ = 1;
    v___x_5539_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__5;
    v___x_5540_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5539_, v___x_5538_);
    return v___x_5540_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__6,
    );
    v___x_5542_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__4,
    );
    v___x_5543_ = lean_string_append(v___x_5542_, v___x_5541_);
    return v___x_5543_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5544_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5545_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__7,
    );
    v___x_5546_ = lean_string_append(v___x_5545_, v___x_5544_);
    return v___x_5546_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson(
    mut v_json_5547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5553_: u8 = 0;
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5559_: u8 = 0;
    let mut v_a_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5563_: u8 = 0;
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut v_a_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5548_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__0;
                v___x_5549_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson_spec__0(v_json_5547_, v___x_5548_);
                if leanh::lean_obj_tag(v___x_5549_) == 0 {
                    v_a_5550_ = leanh::lean_ctor_get(v___x_5549_, 0);
                    v_isSharedCheck_5559_ = (!leanh::lean_is_exclusive(v___x_5549_)) as u8;
                    if v_isSharedCheck_5559_ == 0 {
                        v___x_5552_ = v___x_5549_;
                        v_isShared_5553_ = v_isSharedCheck_5559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5550_);
                        leanh::lean_dec(v___x_5549_);
                        v___x_5552_ = leanh::lean_box(0);
                        v_isShared_5553_ = v_isSharedCheck_5559_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_5549_) == 0 {
                        v_a_5560_ = leanh::lean_ctor_get(v___x_5549_, 0);
                        v_isSharedCheck_5567_ =
                            (!leanh::lean_is_exclusive(v___x_5549_)) as u8;
                        if v_isSharedCheck_5567_ == 0 {
                            v___x_5562_ = v___x_5549_;
                            v_isShared_5563_ = v_isSharedCheck_5567_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5560_);
                            leanh::lean_dec(v___x_5549_);
                            v___x_5562_ = leanh::lean_box(0);
                            v_isShared_5563_ = v_isSharedCheck_5567_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5568_ = leanh::lean_ctor_get(v___x_5549_, 0);
                        v_isSharedCheck_5575_ =
                            (!leanh::lean_is_exclusive(v___x_5549_)) as u8;
                        if v_isSharedCheck_5575_ == 0 {
                            v___x_5570_ = v___x_5549_;
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5568_);
                            leanh::lean_dec(v___x_5549_);
                            v___x_5570_ = leanh::lean_box(0);
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5554_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__8,
                );
                v___x_5555_ = lean_string_append(v___x_5554_, v_a_5550_);
                leanh::lean_dec(v_a_5550_);
                if v_isShared_5553_ == 0 {
                    leanh::lean_ctor_set(v___x_5552_, 0, v___x_5555_);
                    v___x_5557_ = v___x_5552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5555_);
                    v___x_5557_ = v_reuseFailAlloc_5558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5557_;
            }
            3 => {
                if v_isShared_5563_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5562_, 0);
                    v___x_5565_ = v___x_5562_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
                    v___x_5565_ = v_reuseFailAlloc_5566_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5565_;
            }
            5 => {
                if v_isShared_5571_ == 0 {
                    v___x_5573_ = v___x_5570_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionLiteralSupport_toJson(
    mut v_x_5578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5579_ = l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson___closed__0;
    v___x_5580_ = l_Lean_Lsp_instToJsonCodeActionLiteralSupportValueSet_toJson(v_x_5578_);
    v___x_5581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5581_, 0, v___x_5579_);
    leanh::lean_ctor_set(v___x_5581_, 1, v___x_5580_);
    v___x_5582_ = leanh::lean_box(0);
    v___x_5583_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5583_, 0, v___x_5581_);
    leanh::lean_ctor_set(v___x_5583_, 1, v___x_5582_);
    v___x_5584_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5584_, 0, v___x_5583_);
    leanh::lean_ctor_set(v___x_5584_, 1, v___x_5582_);
    v___x_5585_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_5586_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_5584_, v___x_5585_);
    v___x_5587_ = l_Lean_Json_mkObj(v___x_5586_);
    leanh::lean_dec(v___x_5586_);
    return v___x_5587_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_5590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5596_: u8 = 0;
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5600_: u8 = 0;
    let mut v_a_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5604_: u8 = 0;
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5590_) == 0 {
                    v___x_5591_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2___closed__0;
                    return v___x_5591_;
                } else {
                    v___x_5592_ =
                        l_Lean_Lsp_instFromJsonCodeActionLiteralSupport_fromJson(v_x_5590_);
                    if leanh::lean_obj_tag(v___x_5592_) == 0 {
                        v_a_5593_ = leanh::lean_ctor_get(v___x_5592_, 0);
                        v_isSharedCheck_5600_ =
                            (!leanh::lean_is_exclusive(v___x_5592_)) as u8;
                        if v_isSharedCheck_5600_ == 0 {
                            v___x_5595_ = v___x_5592_;
                            v_isShared_5596_ = v_isSharedCheck_5600_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5593_);
                            leanh::lean_dec(v___x_5592_);
                            v___x_5595_ = leanh::lean_box(0);
                            v_isShared_5596_ = v_isSharedCheck_5600_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5601_ = leanh::lean_ctor_get(v___x_5592_, 0);
                        v_isSharedCheck_5609_ =
                            (!leanh::lean_is_exclusive(v___x_5592_)) as u8;
                        if v_isSharedCheck_5609_ == 0 {
                            v___x_5603_ = v___x_5592_;
                            v_isShared_5604_ = v_isSharedCheck_5609_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5601_);
                            leanh::lean_dec(v___x_5592_);
                            v___x_5603_ = leanh::lean_box(0);
                            v_isShared_5604_ = v_isSharedCheck_5609_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5596_ == 0 {
                    v___x_5598_ = v___x_5595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
                    v___x_5598_ = v_reuseFailAlloc_5599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5598_;
            }
            3 => {
                v___x_5605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5605_, 0, v_a_5601_);
                if v_isShared_5604_ == 0 {
                    leanh::lean_ctor_set(v___x_5603_, 0, v___x_5605_);
                    v___x_5607_ = v___x_5603_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 0, v___x_5605_);
                    v___x_5607_ = v_reuseFailAlloc_5608_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__0(
    mut v_j_5610_: *mut leanh::LeanObject,
    mut v_k_5611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5612_ = l_Lean_Json_getObjValD(v_j_5610_, v_k_5611_);
    v___x_5613_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__0_spec__0(v___x_5612_);
    return v___x_5613_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_5614_: *mut leanh::LeanObject,
    mut v_k_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5616_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__0(v_j_5614_, v_k_5615_);
    leanh::lean_dec_ref(v_k_5615_);
    return v_res_5616_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__1_spec__2(
    mut v_x_5617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5623_: u8 = 0;
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5627_: u8 = 0;
    let mut v_a_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5617_) == 0 {
                    v___x_5618_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__1_spec__2___closed__0;
                    return v___x_5618_;
                } else {
                    v___x_5619_ = l_Lean_Lsp_instFromJsonResolveSupport_fromJson(v_x_5617_);
                    if leanh::lean_obj_tag(v___x_5619_) == 0 {
                        v_a_5620_ = leanh::lean_ctor_get(v___x_5619_, 0);
                        v_isSharedCheck_5627_ =
                            (!leanh::lean_is_exclusive(v___x_5619_)) as u8;
                        if v_isSharedCheck_5627_ == 0 {
                            v___x_5622_ = v___x_5619_;
                            v_isShared_5623_ = v_isSharedCheck_5627_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5620_);
                            leanh::lean_dec(v___x_5619_);
                            v___x_5622_ = leanh::lean_box(0);
                            v_isShared_5623_ = v_isSharedCheck_5627_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5628_ = leanh::lean_ctor_get(v___x_5619_, 0);
                        v_isSharedCheck_5636_ =
                            (!leanh::lean_is_exclusive(v___x_5619_)) as u8;
                        if v_isSharedCheck_5636_ == 0 {
                            v___x_5630_ = v___x_5619_;
                            v_isShared_5631_ = v_isSharedCheck_5636_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5628_);
                            leanh::lean_dec(v___x_5619_);
                            v___x_5630_ = leanh::lean_box(0);
                            v_isShared_5631_ = v_isSharedCheck_5636_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5623_ == 0 {
                    v___x_5625_ = v___x_5622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
                    v___x_5625_ = v_reuseFailAlloc_5626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5625_;
            }
            3 => {
                v___x_5632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5632_, 0, v_a_5628_);
                if v_isShared_5631_ == 0 {
                    leanh::lean_ctor_set(v___x_5630_, 0, v___x_5632_);
                    v___x_5634_ = v___x_5630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5635_, 0, v___x_5632_);
                    v___x_5634_ = v_reuseFailAlloc_5635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__1(
    mut v_j_5637_: *mut leanh::LeanObject,
    mut v_k_5638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5639_ = l_Lean_Json_getObjValD(v_j_5637_, v_k_5638_);
    v___x_5640_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__1_spec__2(v___x_5639_);
    return v___x_5640_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__1___boxed(
    mut v_j_5641_: *mut leanh::LeanObject,
    mut v_k_5642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5643_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__1(v_j_5641_, v_k_5642_);
    leanh::lean_dec_ref(v_k_5642_);
    return v_res_5643_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5650_: u8 = 0;
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5650_ = 1;
    v___x_5651_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__2;
    v___x_5652_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5651_, v___x_5650_);
    return v___x_5652_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5653_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__6;
    v___x_5654_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__3,
    );
    v___x_5655_ = lean_string_append(v___x_5654_, v___x_5653_);
    return v___x_5655_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5659_: u8 = 0;
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5659_ = 1;
    v___x_5660_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__6;
    v___x_5661_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5660_, v___x_5659_);
    return v___x_5661_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5662_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__7,
    );
    v___x_5663_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5664_ = lean_string_append(v___x_5663_, v___x_5662_);
    return v___x_5664_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5665_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5666_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__8,
    );
    v___x_5667_ = lean_string_append(v___x_5666_, v___x_5665_);
    return v___x_5667_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5672_: u8 = 0;
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5672_ = 1;
    v___x_5673_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__12;
    v___x_5674_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5673_, v___x_5672_);
    return v___x_5674_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5675_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__13,
    );
    v___x_5676_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5677_ = lean_string_append(v___x_5676_, v___x_5675_);
    return v___x_5677_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5678_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5679_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__14_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__14,
    );
    v___x_5680_ = lean_string_append(v___x_5679_, v___x_5678_);
    return v___x_5680_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5685_: u8 = 0;
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5685_ = 1;
    v___x_5686_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__18;
    v___x_5687_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5686_, v___x_5685_);
    return v___x_5687_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5688_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__19_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__19,
    );
    v___x_5689_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5690_ = lean_string_append(v___x_5689_, v___x_5688_);
    return v___x_5690_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5692_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__20_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__20,
    );
    v___x_5693_ = lean_string_append(v___x_5692_, v___x_5691_);
    return v___x_5693_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_5698_: u8 = 0;
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5698_ = 1;
    v___x_5699_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__24;
    v___x_5700_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5699_, v___x_5698_);
    return v___x_5700_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5701_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__25_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__25,
    );
    v___x_5702_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5703_ = lean_string_append(v___x_5702_, v___x_5701_);
    return v___x_5703_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5704_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5705_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__26_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__26,
    );
    v___x_5706_ = lean_string_append(v___x_5705_, v___x_5704_);
    return v___x_5706_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_5711_: u8 = 0;
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5711_ = 1;
    v___x_5712_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__30;
    v___x_5713_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5712_, v___x_5711_);
    return v___x_5713_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5714_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__31
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__31_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__31,
    );
    v___x_5715_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5716_ = lean_string_append(v___x_5715_, v___x_5714_);
    return v___x_5716_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5717_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5718_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__32
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__32_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__32,
    );
    v___x_5719_ = lean_string_append(v___x_5718_, v___x_5717_);
    return v___x_5719_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_5724_: u8 = 0;
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5724_ = 1;
    v___x_5725_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__36;
    v___x_5726_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5725_, v___x_5724_);
    return v___x_5726_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5727_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__37
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__37_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__37,
    );
    v___x_5728_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5729_ = lean_string_append(v___x_5728_, v___x_5727_);
    return v___x_5729_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5730_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5731_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__38
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__38_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__38,
    );
    v___x_5732_ = lean_string_append(v___x_5731_, v___x_5730_);
    return v___x_5732_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_5737_: u8 = 0;
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = 1;
    v___x_5738_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__42;
    v___x_5739_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5738_, v___x_5737_);
    return v___x_5739_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5740_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__43
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__43_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__43,
    );
    v___x_5741_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__4,
    );
    v___x_5742_ = lean_string_append(v___x_5741_, v___x_5740_);
    return v___x_5742_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5743_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1___closed__11;
    v___x_5744_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__44
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__44_once
        ),
        _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__44,
    );
    v___x_5745_ = lean_string_append(v___x_5744_, v___x_5743_);
    return v___x_5745_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson(
    mut v_json_5746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5752_: u8 = 0;
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5758_: u8 = 0;
    let mut v_a_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_a_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5773_: u8 = 0;
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5779_: u8 = 0;
    let mut v_a_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5787_: u8 = 0;
    let mut v_a_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5794_: u8 = 0;
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5800_: u8 = 0;
    let mut v_a_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5804_: u8 = 0;
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_a_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5815_: u8 = 0;
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5821_: u8 = 0;
    let mut v_a_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5825_: u8 = 0;
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5829_: u8 = 0;
    let mut v_a_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5836_: u8 = 0;
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5842_: u8 = 0;
    let mut v_a_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v___x_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut v_a_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5857_: u8 = 0;
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5863_: u8 = 0;
    let mut v_a_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5867_: u8 = 0;
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5871_: u8 = 0;
    let mut v_a_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5878_: u8 = 0;
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5884_: u8 = 0;
    let mut v_a_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5888_: u8 = 0;
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5892_: u8 = 0;
    let mut v_a_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5896_: u8 = 0;
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5747_ =
                    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__0;
                leanh::lean_inc(v_json_5746_);
                v___x_5748_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_5746_, v___x_5747_);
                if leanh::lean_obj_tag(v___x_5748_) == 0 {
                    leanh::lean_dec(v_json_5746_);
                    v_a_5749_ = leanh::lean_ctor_get(v___x_5748_, 0);
                    v_isSharedCheck_5758_ = (!leanh::lean_is_exclusive(v___x_5748_)) as u8;
                    if v_isSharedCheck_5758_ == 0 {
                        v___x_5751_ = v___x_5748_;
                        v_isShared_5752_ = v_isSharedCheck_5758_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5749_);
                        leanh::lean_dec(v___x_5748_);
                        v___x_5751_ = leanh::lean_box(0);
                        v_isShared_5752_ = v_isSharedCheck_5758_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_5748_) == 0 {
                        leanh::lean_dec(v_json_5746_);
                        v_a_5759_ = leanh::lean_ctor_get(v___x_5748_, 0);
                        v_isSharedCheck_5766_ =
                            (!leanh::lean_is_exclusive(v___x_5748_)) as u8;
                        if v_isSharedCheck_5766_ == 0 {
                            v___x_5761_ = v___x_5748_;
                            v_isShared_5762_ = v_isSharedCheck_5766_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5759_);
                            leanh::lean_dec(v___x_5748_);
                            v___x_5761_ = leanh::lean_box(0);
                            v_isShared_5762_ = v_isSharedCheck_5766_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5767_ = leanh::lean_ctor_get(v___x_5748_, 0);
                        leanh::lean_inc(v_a_5767_);
                        leanh::lean_dec_ref_known(v___x_5748_, 1);
                        v___x_5768_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__10;
                        leanh::lean_inc(v_json_5746_);
                        v___x_5769_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_5746_, v___x_5768_);
                        if leanh::lean_obj_tag(v___x_5769_) == 0 {
                            leanh::lean_dec(v_a_5767_);
                            leanh::lean_dec(v_json_5746_);
                            v_a_5770_ = leanh::lean_ctor_get(v___x_5769_, 0);
                            v_isSharedCheck_5779_ =
                                (!leanh::lean_is_exclusive(v___x_5769_)) as u8;
                            if v_isSharedCheck_5779_ == 0 {
                                v___x_5772_ = v___x_5769_;
                                v_isShared_5773_ = v_isSharedCheck_5779_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5770_);
                                leanh::lean_dec(v___x_5769_);
                                v___x_5772_ = leanh::lean_box(0);
                                v_isShared_5773_ = v_isSharedCheck_5779_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_5769_) == 0 {
                                leanh::lean_dec(v_a_5767_);
                                leanh::lean_dec(v_json_5746_);
                                v_a_5780_ = leanh::lean_ctor_get(v___x_5769_, 0);
                                v_isSharedCheck_5787_ =
                                    (!leanh::lean_is_exclusive(v___x_5769_)) as u8;
                                if v_isSharedCheck_5787_ == 0 {
                                    v___x_5782_ = v___x_5769_;
                                    v_isShared_5783_ = v_isSharedCheck_5787_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5780_);
                                    leanh::lean_dec(v___x_5769_);
                                    v___x_5782_ = leanh::lean_box(0);
                                    v_isShared_5783_ = v_isSharedCheck_5787_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5788_ = leanh::lean_ctor_get(v___x_5769_, 0);
                                leanh::lean_inc(v_a_5788_);
                                leanh::lean_dec_ref_known(v___x_5769_, 1);
                                v___x_5789_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__16;
                                leanh::lean_inc(v_json_5746_);
                                v___x_5790_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_5746_, v___x_5789_);
                                if leanh::lean_obj_tag(v___x_5790_) == 0 {
                                    leanh::lean_dec(v_a_5788_);
                                    leanh::lean_dec(v_a_5767_);
                                    leanh::lean_dec(v_json_5746_);
                                    v_a_5791_ = leanh::lean_ctor_get(v___x_5790_, 0);
                                    v_isSharedCheck_5800_ =
                                        (!leanh::lean_is_exclusive(v___x_5790_)) as u8;
                                    if v_isSharedCheck_5800_ == 0 {
                                        v___x_5793_ = v___x_5790_;
                                        v_isShared_5794_ = v_isSharedCheck_5800_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5791_);
                                        leanh::lean_dec(v___x_5790_);
                                        v___x_5793_ = leanh::lean_box(0);
                                        v_isShared_5794_ = v_isSharedCheck_5800_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_5790_) == 0 {
                                        leanh::lean_dec(v_a_5788_);
                                        leanh::lean_dec(v_a_5767_);
                                        leanh::lean_dec(v_json_5746_);
                                        v_a_5801_ = leanh::lean_ctor_get(v___x_5790_, 0);
                                        v_isSharedCheck_5808_ =
                                            (!leanh::lean_is_exclusive(v___x_5790_)) as u8;
                                        if v_isSharedCheck_5808_ == 0 {
                                            v___x_5803_ = v___x_5790_;
                                            v_isShared_5804_ = v_isSharedCheck_5808_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5801_);
                                            leanh::lean_dec(v___x_5790_);
                                            v___x_5803_ = leanh::lean_box(0);
                                            v_isShared_5804_ = v_isSharedCheck_5808_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5809_ = leanh::lean_ctor_get(v___x_5790_, 0);
                                        leanh::lean_inc(v_a_5809_);
                                        leanh::lean_dec_ref_known(v___x_5790_, 1);
                                        v___x_5810_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__22;
                                        leanh::lean_inc(v_json_5746_);
                                        v___x_5811_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_5746_, v___x_5810_);
                                        if leanh::lean_obj_tag(v___x_5811_) == 0 {
                                            leanh::lean_dec(v_a_5809_);
                                            leanh::lean_dec(v_a_5788_);
                                            leanh::lean_dec(v_a_5767_);
                                            leanh::lean_dec(v_json_5746_);
                                            v_a_5812_ = leanh::lean_ctor_get(v___x_5811_, 0);
                                            v_isSharedCheck_5821_ =
                                                (!leanh::lean_is_exclusive(v___x_5811_))
                                                    as u8;
                                            if v_isSharedCheck_5821_ == 0 {
                                                v___x_5814_ = v___x_5811_;
                                                v_isShared_5815_ = v_isSharedCheck_5821_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_5812_);
                                                leanh::lean_dec(v___x_5811_);
                                                v___x_5814_ = leanh::lean_box(0);
                                                v_isShared_5815_ = v_isSharedCheck_5821_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_5811_) == 0 {
                                                leanh::lean_dec(v_a_5809_);
                                                leanh::lean_dec(v_a_5788_);
                                                leanh::lean_dec(v_a_5767_);
                                                leanh::lean_dec(v_json_5746_);
                                                v_a_5822_ =
                                                    leanh::lean_ctor_get(v___x_5811_, 0);
                                                v_isSharedCheck_5829_ =
                                                    (!leanh::lean_is_exclusive(v___x_5811_))
                                                        as u8;
                                                if v_isSharedCheck_5829_ == 0 {
                                                    v___x_5824_ = v___x_5811_;
                                                    v_isShared_5825_ = v_isSharedCheck_5829_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5822_);
                                                    leanh::lean_dec(v___x_5811_);
                                                    v___x_5824_ = leanh::lean_box(0);
                                                    v_isShared_5825_ = v_isSharedCheck_5829_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5830_ =
                                                    leanh::lean_ctor_get(v___x_5811_, 0);
                                                leanh::lean_inc(v_a_5830_);
                                                leanh::lean_dec_ref_known(v___x_5811_, 1);
                                                v___x_5831_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__28;
                                                leanh::lean_inc(v_json_5746_);
                                                v___x_5832_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionContext_fromJson_spec__0_spec__0_spec__1_spec__8(v_json_5746_, v___x_5831_);
                                                if leanh::lean_obj_tag(v___x_5832_) == 0 {
                                                    leanh::lean_dec(v_a_5830_);
                                                    leanh::lean_dec(v_a_5809_);
                                                    leanh::lean_dec(v_a_5788_);
                                                    leanh::lean_dec(v_a_5767_);
                                                    leanh::lean_dec(v_json_5746_);
                                                    v_a_5833_ =
                                                        leanh::lean_ctor_get(v___x_5832_, 0);
                                                    v_isSharedCheck_5842_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_5832_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5842_ == 0 {
                                                        v___x_5835_ = v___x_5832_;
                                                        v_isShared_5836_ = v_isSharedCheck_5842_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_5833_);
                                                        leanh::lean_dec(v___x_5832_);
                                                        v___x_5835_ = leanh::lean_box(0);
                                                        v_isShared_5836_ = v_isSharedCheck_5842_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_5832_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_5830_);
                                                        leanh::lean_dec(v_a_5809_);
                                                        leanh::lean_dec(v_a_5788_);
                                                        leanh::lean_dec(v_a_5767_);
                                                        leanh::lean_dec(v_json_5746_);
                                                        v_a_5843_ = leanh::lean_ctor_get(
                                                            v___x_5832_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5850_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_5832_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5850_ == 0 {
                                                            v___x_5845_ = v___x_5832_;
                                                            v_isShared_5846_ =
                                                                v_isSharedCheck_5850_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_5843_);
                                                            leanh::lean_dec(v___x_5832_);
                                                            v___x_5845_ = leanh::lean_box(0);
                                                            v_isShared_5846_ =
                                                                v_isSharedCheck_5850_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_5851_ = leanh::lean_ctor_get(
                                                            v___x_5832_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_5851_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_5832_,
                                                            1,
                                                        );
                                                        v___x_5852_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__34;
                                                        leanh::lean_inc(v_json_5746_);
                                                        v___x_5853_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__0(v_json_5746_, v___x_5852_);
                                                        if leanh::lean_obj_tag(v___x_5853_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_5851_);
                                                            leanh::lean_dec(v_a_5830_);
                                                            leanh::lean_dec(v_a_5809_);
                                                            leanh::lean_dec(v_a_5788_);
                                                            leanh::lean_dec(v_a_5767_);
                                                            leanh::lean_dec(v_json_5746_);
                                                            v_a_5854_ = leanh::lean_ctor_get(
                                                                v___x_5853_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5863_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_5853_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5863_ == 0 {
                                                                v___x_5856_ = v___x_5853_;
                                                                v_isShared_5857_ =
                                                                    v_isSharedCheck_5863_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_5854_);
                                                                leanh::lean_dec(v___x_5853_);
                                                                v___x_5856_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5857_ =
                                                                    v_isSharedCheck_5863_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v___x_5853_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec(v_a_5851_);
                                                                leanh::lean_dec(v_a_5830_);
                                                                leanh::lean_dec(v_a_5809_);
                                                                leanh::lean_dec(v_a_5788_);
                                                                leanh::lean_dec(v_a_5767_);
                                                                leanh::lean_dec(
                                                                    v_json_5746_,
                                                                );
                                                                v_a_5864_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5853_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5871_ = (!leanh::lean_is_exclusive(v___x_5853_)) as u8;
                                                                if v_isSharedCheck_5871_ == 0 {
                                                                    v___x_5866_ = v___x_5853_;
                                                                    v_isShared_5867_ =
                                                                        v_isSharedCheck_5871_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_5864_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_5853_,
                                                                    );
                                                                    v___x_5866_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_5867_ =
                                                                        v_isSharedCheck_5871_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_5872_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5853_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_5872_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_5853_,
                                                                    1,
                                                                );
                                                                v___x_5873_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__40;
                                                                v___x_5874_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson_spec__1(v_json_5746_, v___x_5873_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_5874_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec(
                                                                        v_a_5872_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5851_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5830_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5809_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5788_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5767_,
                                                                    );
                                                                    v_a_5875_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_5874_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5884_ = (!leanh::lean_is_exclusive(v___x_5874_)) as u8;
                                                                    if v_isSharedCheck_5884_ == 0 {
                                                                        v___x_5877_ = v___x_5874_;
                                                                        v_isShared_5878_ =
                                                                            v_isSharedCheck_5884_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_5875_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_5874_,
                                                                        );
                                                                        v___x_5877_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5878_ =
                                                                            v_isSharedCheck_5884_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_5874_,
                                                                    ) == 0
                                                                    {
                                                                        leanh::lean_dec(
                                                                            v_a_5872_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5851_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5830_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5809_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5788_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5767_,
                                                                        );
                                                                        v_a_5885_ = leanh::lean_ctor_get(v___x_5874_, 0);
                                                                        v_isSharedCheck_5892_ = (!leanh::lean_is_exclusive(v___x_5874_)) as u8;
                                                                        if v_isSharedCheck_5892_
                                                                            == 0
                                                                        {
                                                                            v___x_5887_ =
                                                                                v___x_5874_;
                                                                            v_isShared_5888_ = v_isSharedCheck_5892_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_5885_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_5874_,
                                                                            );
                                                                            v___x_5887_ = leanh::lean_box(0);
                                                                            v_isShared_5888_ = v_isSharedCheck_5892_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_5893_ = leanh::lean_ctor_get(v___x_5874_, 0);
                                                                        v_isSharedCheck_5901_ = (!leanh::lean_is_exclusive(v___x_5874_)) as u8;
                                                                        if v_isSharedCheck_5901_
                                                                            == 0
                                                                        {
                                                                            v___x_5895_ =
                                                                                v___x_5874_;
                                                                            v_isShared_5896_ = v_isSharedCheck_5901_;
                                                                            state = 29;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_5893_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_5874_,
                                                                            );
                                                                            v___x_5895_ = leanh::lean_box(0);
                                                                            v_isShared_5896_ = v_isSharedCheck_5901_;
                                                                            state = 29;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5753_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__9_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__9);
                v___x_5754_ = lean_string_append(v___x_5753_, v_a_5749_);
                leanh::lean_dec(v_a_5749_);
                if v_isShared_5752_ == 0 {
                    leanh::lean_ctor_set(v___x_5751_, 0, v___x_5754_);
                    v___x_5756_ = v___x_5751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5754_);
                    v___x_5756_ = v_reuseFailAlloc_5757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5756_;
            }
            3 => {
                if v_isShared_5762_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5761_, 0);
                    v___x_5764_ = v___x_5761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
                    v___x_5764_ = v_reuseFailAlloc_5765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5764_;
            }
            5 => {
                v___x_5774_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__15), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__15_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__15);
                v___x_5775_ = lean_string_append(v___x_5774_, v_a_5770_);
                leanh::lean_dec(v_a_5770_);
                if v_isShared_5773_ == 0 {
                    leanh::lean_ctor_set(v___x_5772_, 0, v___x_5775_);
                    v___x_5777_ = v___x_5772_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5778_, 0, v___x_5775_);
                    v___x_5777_ = v_reuseFailAlloc_5778_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5777_;
            }
            7 => {
                if v_isShared_5783_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5782_, 0);
                    v___x_5785_ = v___x_5782_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5786_, 0, v_a_5780_);
                    v___x_5785_ = v_reuseFailAlloc_5786_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5785_;
            }
            9 => {
                v___x_5795_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__21), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__21_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__21);
                v___x_5796_ = lean_string_append(v___x_5795_, v_a_5791_);
                leanh::lean_dec(v_a_5791_);
                if v_isShared_5794_ == 0 {
                    leanh::lean_ctor_set(v___x_5793_, 0, v___x_5796_);
                    v___x_5798_ = v___x_5793_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5796_);
                    v___x_5798_ = v_reuseFailAlloc_5799_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5798_;
            }
            11 => {
                if v_isShared_5804_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5803_, 0);
                    v___x_5806_ = v___x_5803_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_a_5801_);
                    v___x_5806_ = v_reuseFailAlloc_5807_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5806_;
            }
            13 => {
                v___x_5816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__27), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__27_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__27);
                v___x_5817_ = lean_string_append(v___x_5816_, v_a_5812_);
                leanh::lean_dec(v_a_5812_);
                if v_isShared_5815_ == 0 {
                    leanh::lean_ctor_set(v___x_5814_, 0, v___x_5817_);
                    v___x_5819_ = v___x_5814_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5820_, 0, v___x_5817_);
                    v___x_5819_ = v_reuseFailAlloc_5820_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5819_;
            }
            15 => {
                if v_isShared_5825_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5824_, 0);
                    v___x_5827_ = v___x_5824_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5822_);
                    v___x_5827_ = v_reuseFailAlloc_5828_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5827_;
            }
            17 => {
                v___x_5837_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__33), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__33_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__33);
                v___x_5838_ = lean_string_append(v___x_5837_, v_a_5833_);
                leanh::lean_dec(v_a_5833_);
                if v_isShared_5836_ == 0 {
                    leanh::lean_ctor_set(v___x_5835_, 0, v___x_5838_);
                    v___x_5840_ = v___x_5835_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5838_);
                    v___x_5840_ = v_reuseFailAlloc_5841_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5840_;
            }
            19 => {
                if v_isShared_5846_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5845_, 0);
                    v___x_5848_ = v___x_5845_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
                    v___x_5848_ = v_reuseFailAlloc_5849_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5848_;
            }
            21 => {
                v___x_5858_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__39), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__39_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__39);
                v___x_5859_ = lean_string_append(v___x_5858_, v_a_5854_);
                leanh::lean_dec(v_a_5854_);
                if v_isShared_5857_ == 0 {
                    leanh::lean_ctor_set(v___x_5856_, 0, v___x_5859_);
                    v___x_5861_ = v___x_5856_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___x_5859_);
                    v___x_5861_ = v_reuseFailAlloc_5862_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5861_;
            }
            23 => {
                if v_isShared_5867_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5866_, 0);
                    v___x_5869_ = v___x_5866_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
                    v___x_5869_ = v_reuseFailAlloc_5870_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5869_;
            }
            25 => {
                v___x_5879_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__45), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__45_once), _init_l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__45);
                v___x_5880_ = lean_string_append(v___x_5879_, v_a_5875_);
                leanh::lean_dec(v_a_5875_);
                if v_isShared_5878_ == 0 {
                    leanh::lean_ctor_set(v___x_5877_, 0, v___x_5880_);
                    v___x_5882_ = v___x_5877_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5883_, 0, v___x_5880_);
                    v___x_5882_ = v_reuseFailAlloc_5883_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5882_;
            }
            27 => {
                if v_isShared_5888_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5887_, 0);
                    v___x_5890_ = v___x_5887_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_a_5885_);
                    v___x_5890_ = v_reuseFailAlloc_5891_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5890_;
            }
            29 => {
                v___x_5897_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                leanh::lean_ctor_set(v___x_5897_, 0, v_a_5767_);
                leanh::lean_ctor_set(v___x_5897_, 1, v_a_5788_);
                leanh::lean_ctor_set(v___x_5897_, 2, v_a_5809_);
                leanh::lean_ctor_set(v___x_5897_, 3, v_a_5830_);
                leanh::lean_ctor_set(v___x_5897_, 4, v_a_5851_);
                leanh::lean_ctor_set(v___x_5897_, 5, v_a_5872_);
                leanh::lean_ctor_set(v___x_5897_, 6, v_a_5893_);
                if v_isShared_5896_ == 0 {
                    leanh::lean_ctor_set(v___x_5895_, 0, v___x_5897_);
                    v___x_5899_ = v___x_5895_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5897_);
                    v___x_5899_ = v_reuseFailAlloc_5900_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson_spec__0(
    mut v_k_5904_: *mut leanh::LeanObject,
    mut v_x_5905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5905_) == 0 {
        let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_5904_);
        v___x_5906_ = leanh::lean_box(0);
        return v___x_5906_;
    } else {
        let mut v_val_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5907_ = leanh::lean_ctor_get(v_x_5905_, 0);
        leanh::lean_inc(v_val_5907_);
        leanh::lean_dec_ref_known(v_x_5905_, 1);
        v___x_5908_ = l_Lean_Lsp_instToJsonCodeActionLiteralSupport_toJson(v_val_5907_);
        v___x_5909_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5909_, 0, v_k_5904_);
        leanh::lean_ctor_set(v___x_5909_, 1, v___x_5908_);
        v___x_5910_ = leanh::lean_box(0);
        v___x_5911_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5911_, 0, v___x_5909_);
        leanh::lean_ctor_set(v___x_5911_, 1, v___x_5910_);
        return v___x_5911_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson_spec__1(
    mut v_k_5912_: *mut leanh::LeanObject,
    mut v_x_5913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5913_) == 0 {
        let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_5912_);
        v___x_5914_ = leanh::lean_box(0);
        return v___x_5914_;
    } else {
        let mut v_val_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5915_ = leanh::lean_ctor_get(v_x_5913_, 0);
        leanh::lean_inc(v_val_5915_);
        leanh::lean_dec_ref_known(v_x_5913_, 1);
        v___x_5916_ = l_Lean_Lsp_instToJsonResolveSupport_toJson(v_val_5915_);
        v___x_5917_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5917_, 0, v_k_5912_);
        leanh::lean_ctor_set(v___x_5917_, 1, v___x_5916_);
        v___x_5918_ = leanh::lean_box(0);
        v___x_5919_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5919_, 0, v___x_5917_);
        leanh::lean_ctor_set(v___x_5919_, 1, v___x_5918_);
        return v___x_5919_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson(
    mut v_x_5920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dynamicRegistration_x3f_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreferredSupport_x3f_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disabledSupport_x3f_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dataSupport_x3f_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_honorsChangeAnnotations_x3f_5925_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_codeActionLiteralSupport_x3f_5926_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_resolveSupport_x3f_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dynamicRegistration_x3f_5921_ = leanh::lean_ctor_get(v_x_5920_, 0);
    leanh::lean_inc(v_dynamicRegistration_x3f_5921_);
    v_isPreferredSupport_x3f_5922_ = leanh::lean_ctor_get(v_x_5920_, 1);
    leanh::lean_inc(v_isPreferredSupport_x3f_5922_);
    v_disabledSupport_x3f_5923_ = leanh::lean_ctor_get(v_x_5920_, 2);
    leanh::lean_inc(v_disabledSupport_x3f_5923_);
    v_dataSupport_x3f_5924_ = leanh::lean_ctor_get(v_x_5920_, 3);
    leanh::lean_inc(v_dataSupport_x3f_5924_);
    v_honorsChangeAnnotations_x3f_5925_ = leanh::lean_ctor_get(v_x_5920_, 4);
    leanh::lean_inc(v_honorsChangeAnnotations_x3f_5925_);
    v_codeActionLiteralSupport_x3f_5926_ = leanh::lean_ctor_get(v_x_5920_, 5);
    leanh::lean_inc(v_codeActionLiteralSupport_x3f_5926_);
    v_resolveSupport_x3f_5927_ = leanh::lean_ctor_get(v_x_5920_, 6);
    leanh::lean_inc(v_resolveSupport_x3f_5927_);
    leanh::lean_dec_ref(v_x_5920_);
    v___x_5928_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__0;
    v___x_5929_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_5928_, v_dynamicRegistration_x3f_5921_);
    leanh::lean_dec(v_dynamicRegistration_x3f_5921_);
    v___x_5930_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__10;
    v___x_5931_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_5930_, v_isPreferredSupport_x3f_5922_);
    leanh::lean_dec(v_isPreferredSupport_x3f_5922_);
    v___x_5932_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__16;
    v___x_5933_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_5932_, v_disabledSupport_x3f_5923_);
    leanh::lean_dec(v_disabledSupport_x3f_5923_);
    v___x_5934_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__22;
    v___x_5935_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_5934_, v_dataSupport_x3f_5924_);
    leanh::lean_dec(v_dataSupport_x3f_5924_);
    v___x_5936_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__28;
    v___x_5937_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0_spec__4(v___x_5936_, v_honorsChangeAnnotations_x3f_5925_);
    leanh::lean_dec(v_honorsChangeAnnotations_x3f_5925_);
    v___x_5938_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__34;
    v___x_5939_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson_spec__0(
            v___x_5938_,
            v_codeActionLiteralSupport_x3f_5926_,
        );
    v___x_5940_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson___closed__40;
    v___x_5941_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson_spec__1(
            v___x_5940_,
            v_resolveSupport_x3f_5927_,
        );
    v___x_5942_ = leanh::lean_box(0);
    v___x_5943_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5943_, 0, v___x_5941_);
    leanh::lean_ctor_set(v___x_5943_, 1, v___x_5942_);
    v___x_5944_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5944_, 0, v___x_5939_);
    leanh::lean_ctor_set(v___x_5944_, 1, v___x_5943_);
    v___x_5945_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5945_, 0, v___x_5937_);
    leanh::lean_ctor_set(v___x_5945_, 1, v___x_5944_);
    v___x_5946_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5946_, 0, v___x_5935_);
    leanh::lean_ctor_set(v___x_5946_, 1, v___x_5945_);
    v___x_5947_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5947_, 0, v___x_5933_);
    leanh::lean_ctor_set(v___x_5947_, 1, v___x_5946_);
    v___x_5948_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5948_, 0, v___x_5931_);
    leanh::lean_ctor_set(v___x_5948_, 1, v___x_5947_);
    v___x_5949_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5949_, 0, v___x_5929_);
    leanh::lean_ctor_set(v___x_5949_, 1, v___x_5948_);
    v___x_5950_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__0_spec__0___closed__0;
    v___x_5951_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCodeActionContext_toJson_spec__3(v___x_5949_, v___x_5950_);
    v___x_5952_ = l_Lean_Json_mkObj(v___x_5951_);
    leanh::lean_dec(v___x_5951_);
    return v___x_5952_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_CodeActions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_CodeActions(
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
pub unsafe fn initialize_Lean_Data_Lsp_CodeActions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_CodeActions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_CodeActions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_CodeActions(builtin);
}