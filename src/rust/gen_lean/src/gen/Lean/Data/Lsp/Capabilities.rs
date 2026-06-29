// Lean compiler output
// Module: Lean.Data.Lsp.Capabilities
// Imports: Lean.Data.JsonRpc Lean.Data.Lsp.LanguageFeatures Lean.Data.Lsp.CodeActions Lean.Data.Lsp.Extra
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::JsonRpc::{
    initialize_Lean_Data_JsonRpc, runtime_initialize_Lean_Data_JsonRpc,
};
use crate::r#gen::Lean::Data::Lsp::CodeActions::{
    initialize_Lean_Data_Lsp_CodeActions,
    l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson,
    l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson,
    l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson,
    l_Lean_Lsp_instToJsonCodeActionOptions_toJson, runtime_initialize_Lean_Data_Lsp_CodeActions,
};
use crate::r#gen::Lean::Data::Lsp::Extra::{
    initialize_Lean_Data_Lsp_Extra, l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson,
    l_Lean_Lsp_instFromJsonRpcOptions_fromJson, l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson,
    l_Lean_Lsp_instToJsonRpcOptions_toJson, runtime_initialize_Lean_Data_Lsp_Extra,
};
use crate::r#gen::Lean::Data::Lsp::LanguageFeatures::{
    initialize_Lean_Data_Lsp_LanguageFeatures, l_Lean_Lsp_instFromJsonCompletionOptions_fromJson,
    l_Lean_Lsp_instFromJsonDocumentColorOptions_fromJson,
    l_Lean_Lsp_instFromJsonInlayHintClientCapabilities_fromJson,
    l_Lean_Lsp_instFromJsonInlayHintOptions_fromJson,
    l_Lean_Lsp_instFromJsonRenameOptions_fromJson,
    l_Lean_Lsp_instFromJsonSemanticTokensOptions_fromJson,
    l_Lean_Lsp_instFromJsonSignatureHelpOptions_fromJson,
    l_Lean_Lsp_instToJsonCompletionOptions_toJson,
    l_Lean_Lsp_instToJsonDocumentColorOptions_toJson,
    l_Lean_Lsp_instToJsonInlayHintClientCapabilities_toJson,
    l_Lean_Lsp_instToJsonInlayHintOptions_toJson, l_Lean_Lsp_instToJsonRenameOptions_toJson,
    l_Lean_Lsp_instToJsonSemanticTokensOptions_toJson,
    l_Lean_Lsp_instToJsonSignatureHelpOptions_toJson,
    runtime_initialize_Lean_Data_Lsp_LanguageFeatures,
};
use crate::r#gen::Lean::Data::Lsp::TextSync::{
    l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson,
    l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson,
};
use crate::r#gen::Lean::Server::Rpc::Basic::{
    l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson, l_Lean_Lsp_instToJsonRpcWireFormat_toJson,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::lean_array_to_list;
pub static l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 110, 115, 101, 114, 116, 82, 101, 112, 108, 97, 99, 101, 83, 117, 112, 112, 111, 114,
        116, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCompletionItemCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 73, 116, 101, 109, 67, 97, 112, 97, 98,
        105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        17464299465025823400 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        105, 110, 115, 101, 114, 116, 82, 101, 112, 108, 97, 99, 101, 83, 117, 112, 112, 111, 114,
        116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        4147471623459836284 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCompletionItemCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 73, 116, 101, 109, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCompletionClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 67, 108, 105, 101, 110, 116, 67, 97, 112,
        97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15138835640874201723 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 73, 116, 101, 109, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        4963580279542798484 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCompletionClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 110, 108, 97, 121, 72, 105, 110, 116, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonTextDocumentClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 67, 108, 105, 101, 110, 116, 67,
        97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15825155567808153644 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        2415392306143979219 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        10780719447217998112 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 108, 97, 121, 72, 105, 110, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        8789523576692371008 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 117, 112, 112, 111, 114, 116, 0],
};
static mut l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonShowDocumentClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        83, 104, 111, 119, 68, 111, 99, 117, 109, 101, 110, 116, 67, 108, 105, 101, 110, 116, 67,
        97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11433306020704084914 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15347348034595664290 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [115, 104, 111, 119, 68, 111, 99, 117, 109, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonWindowClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        87, 105, 110, 100, 111, 119, 67, 108, 105, 101, 110, 116, 67, 97, 112, 97, 98, 105, 108,
        105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17015919995115081806 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 104, 111, 119, 68, 111, 99, 117, 109, 101, 110, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        3094627890605504356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWindowClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        103, 114, 111, 117, 112, 115, 79, 110, 76, 97, 98, 101, 108, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonChangeAnnotationSupport: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        67, 104, 97, 110, 103, 101, 65, 110, 110, 111, 116, 97, 116, 105, 111, 110, 83, 117, 112,
        112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5581183322240961869 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        103, 114, 111, 117, 112, 115, 79, 110, 76, 97, 98, 101, 108, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        16384624139328773970 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonChangeAnnotationSupport: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        100, 111, 99, 117, 109, 101, 110, 116, 67, 104, 97, 110, 103, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        99, 104, 97, 110, 103, 101, 65, 110, 110, 111, 116, 97, 116, 105, 111, 110, 83, 117, 112,
        112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        114, 101, 115, 111, 117, 114, 99, 101, 79, 112, 101, 114, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
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
        87, 111, 114, 107, 115, 112, 97, 99, 101, 69, 100, 105, 116, 67, 108, 105, 101, 110, 116,
        67, 97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        8052567355273933442 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        100, 111, 99, 117, 109, 101, 110, 116, 67, 104, 97, 110, 103, 101, 115, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        7660261954741923170 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        99, 104, 97, 110, 103, 101, 65, 110, 110, 111, 116, 97, 116, 105, 111, 110, 83, 117, 112,
        112, 111, 114, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        679732866322111590 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        114, 101, 115, 111, 117, 114, 99, 101, 79, 112, 101, 114, 97, 116, 105, 111, 110, 115, 63,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        4182391849625592706 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 112, 112, 108, 121, 69, 100, 105, 116, 0],
};
static mut l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        119, 111, 114, 107, 115, 112, 97, 99, 101, 69, 100, 105, 116, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonWorkspaceClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        87, 111, 114, 107, 115, 112, 97, 99, 101, 67, 108, 105, 101, 110, 116, 67, 97, 112, 97, 98,
        105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17705586535119145597 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [97, 112, 112, 108, 121, 69, 100, 105, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        11825444899619635577 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        119, 111, 114, 107, 115, 112, 97, 99, 101, 69, 100, 105, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        16597517094849894409 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 68, 105, 97, 103, 110, 111, 115, 116,
        105, 99, 83, 117, 112, 112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        115, 105, 108, 101, 110, 116, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 83, 117, 112,
        112, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        114, 112, 99, 87, 105, 114, 101, 70, 111, 114, 109, 97, 116, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 67, 108, 105, 101, 110, 116, 67, 97, 112, 97, 98, 105, 108, 105, 116,
        105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        756221595692236465 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        105, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 68, 105, 97, 103, 110, 111, 115, 116,
        105, 99, 83, 117, 112, 112, 111, 114, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        12347409447873725125 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        115, 105, 108, 101, 110, 116, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 83, 117, 112,
        112, 111, 114, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        2284112806072760941 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        114, 112, 99, 87, 105, 114, 101, 70, 111, 114, 109, 97, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        11967579340742895206 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [119, 105, 110, 100, 111, 119, 0],
};
static mut l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [119, 111, 114, 107, 115, 112, 97, 99, 101, 0],
};
static mut l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 101, 97, 110, 0],
};
static mut l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonClientCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonClientCapabilities___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        67, 108, 105, 101, 110, 116, 67, 97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5727134124778905985 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
        1801102838159436098 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [119, 105, 110, 100, 111, 119, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9_value)
            as *mut crate::leanh::LeanObject,
        6591807397156760927 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 111, 114, 107, 115, 112, 97, 99, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14_value)
            as *mut crate::leanh::LeanObject,
        14779691715263820291 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [108, 101, 97, 110, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19_value)
            as *mut crate::leanh::LeanObject,
        14275066456763359601 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonClientCapabilities___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonClientCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        109, 111, 100, 117, 108, 101, 72, 105, 101, 114, 97, 114, 99, 104, 121, 80, 114, 111, 118,
        105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 83, 101, 114, 118, 101, 114, 67, 97, 112, 97, 98, 105, 108, 105, 116,
        105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        907102490048986040 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        109, 111, 100, 117, 108, 101, 72, 105, 101, 114, 97, 114, 99, 104, 121, 80, 114, 111, 118,
        105, 100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        7437221519932776026 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 112, 99, 80, 114, 111, 118, 105, 100, 101, 114, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [114, 112, 99, 80, 114, 111, 118, 105, 100, 101, 114, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        5611654865711834604 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanServerCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanServerCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 83, 121, 110, 99, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        104, 111, 118, 101, 114, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        100, 111, 99, 117, 109, 101, 110, 116, 72, 105, 103, 104, 108, 105, 103, 104, 116, 80, 114,
        111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        100, 111, 99, 117, 109, 101, 110, 116, 83, 121, 109, 98, 111, 108, 80, 114, 111, 118, 105,
        100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114,
        0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        116, 121, 112, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 80, 114, 111, 118,
        105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        114, 101, 102, 101, 114, 101, 110, 99, 101, 115, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        99, 97, 108, 108, 72, 105, 101, 114, 97, 114, 99, 104, 121, 80, 114, 111, 118, 105, 100,
        101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        114, 101, 110, 97, 109, 101, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        119, 111, 114, 107, 115, 112, 97, 99, 101, 83, 121, 109, 98, 111, 108, 80, 114, 111, 118,
        105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        102, 111, 108, 100, 105, 110, 103, 82, 97, 110, 103, 101, 80, 114, 111, 118, 105, 100, 101,
        114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        115, 101, 109, 97, 110, 116, 105, 99, 84, 111, 107, 101, 110, 115, 80, 114, 111, 118, 105,
        100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        105, 110, 108, 97, 121, 72, 105, 110, 116, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        115, 105, 103, 110, 97, 116, 117, 114, 101, 72, 101, 108, 112, 80, 114, 111, 118, 105, 100,
        101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        99, 111, 108, 111, 114, 80, 114, 111, 118, 105, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 120, 112, 101, 114, 105, 109, 101, 110, 116, 97, 108, 0],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonServerCapabilities_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonServerCapabilities___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonServerCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        83, 101, 114, 118, 101, 114, 67, 97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6297634172192931594 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 83, 121, 110, 99, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
        15067064454058721009 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 63,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9_value)
            as *mut crate::leanh::LeanObject,
        3944384203641612876 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18095661268397618176 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3_value)
            as *mut crate::leanh::LeanObject,
        1213351240577164003 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16104892146493075686 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3980288438418220582 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6_value)
            as *mut crate::leanh::LeanObject,
        13522848839790619986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7_value)
            as *mut crate::leanh::LeanObject,
        11387787157426769309 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8_value)
            as *mut crate::leanh::LeanObject,
        12616514027146993754 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9_value)
            as *mut crate::leanh::LeanObject,
        15703389469843110140 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        114, 101, 110, 97, 109, 101, 80, 114, 111, 118, 105, 100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46_value)
            as *mut crate::leanh::LeanObject,
        8151968516154898339 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11_value)
            as *mut crate::leanh::LeanObject,
        1523806251088820109 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12_value)
            as *mut crate::leanh::LeanObject,
        291963926766054028 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        115, 101, 109, 97, 110, 116, 105, 99, 84, 111, 107, 101, 110, 115, 80, 114, 111, 118, 105,
        100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59_value)
            as *mut crate::leanh::LeanObject,
        14436169570748488559 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64_value)
            as *mut crate::leanh::LeanObject,
        7095079082484331834 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        105, 110, 108, 97, 121, 72, 105, 110, 116, 80, 114, 111, 118, 105, 100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69_value)
            as *mut crate::leanh::LeanObject,
        12934655174597824157 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        115, 105, 103, 110, 97, 116, 117, 114, 101, 72, 101, 108, 112, 80, 114, 111, 118, 105, 100,
        101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74_value)
            as *mut crate::leanh::LeanObject,
        493649595047005953 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 111, 108, 111, 114, 80, 114, 111, 118, 105, 100, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79_value)
            as *mut crate::leanh::LeanObject,
        14024689096226447734 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        101, 120, 112, 101, 114, 105, 109, 101, 110, 116, 97, 108, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84_value)
            as *mut crate::leanh::LeanObject,
        6549575833794781025 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerCapabilities___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonServerCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonServerCapabilities___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonServerCapabilities: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerCapabilities___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
    mut v_k_3021_: *mut crate::leanh::LeanObject,
    mut v_x_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3022_) == 0 {
        let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3021_);
        v___x_3023_ = crate::leanh::lean_box(0);
        return v___x_3023_;
    } else {
        let mut v_val_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3026_: u8 = 0;
        let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3024_ = crate::leanh::lean_ctor_get(v_x_3022_, 0);
        v___x_3025_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
        v___x_3026_ = (crate::leanh::lean_unbox(v_val_3024_) as u8);
        crate::leanh::lean_ctor_set_uint8(v___x_3025_, 0 as u32, v___x_3026_);
        v___x_3027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3027_, 0, v_k_3021_);
        crate::leanh::lean_ctor_set(v___x_3027_, 1, v___x_3025_);
        v___x_3028_ = crate::leanh::lean_box(0);
        v___x_3029_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3029_, 0, v___x_3027_);
        crate::leanh::lean_ctor_set(v___x_3029_, 1, v___x_3028_);
        return v___x_3029_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0___boxed(
    mut v_k_3030_: *mut crate::leanh::LeanObject,
    mut v_x_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
            v_k_3030_, v_x_3031_,
        );
    crate::leanh::lean_dec(v_x_3031_);
    return v_res_3032_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3033_) == 0 {
                    v___x_3035_ = lean_array_to_list(v_a_3034_);
                    return v___x_3035_;
                } else {
                    v_head_3036_ = crate::leanh::lean_ctor_get(v_a_3033_, 0);
                    crate::leanh::lean_inc(v_head_3036_);
                    v_tail_3037_ = crate::leanh::lean_ctor_get(v_a_3033_, 1);
                    crate::leanh::lean_inc(v_tail_3037_);
                    crate::leanh::lean_dec_ref_known(v_a_3033_, 2);
                    v___x_3038_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3034_,
                        v_head_3036_,
                    );
                    v_a_3033_ = v_tail_3037_;
                    v_a_3034_ = v___x_3038_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(
    mut v_x_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3044_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0;
    v___x_3045_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
            v___x_3044_,
            v_x_3043_,
        );
    v___x_3046_ = crate::leanh::lean_box(0);
    v___x_3047_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3047_, 0, v___x_3045_);
    crate::leanh::lean_ctor_set(v___x_3047_, 1, v___x_3046_);
    v___x_3048_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3049_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3047_, v___x_3048_);
    v___x_3050_ = l_Lean_Json_mkObj(v___x_3049_);
    crate::leanh::lean_dec(v___x_3049_);
    return v___x_3050_;
}
pub unsafe fn l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___boxed(
    mut v_x_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3052_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(v_x_3051_);
    crate::leanh::lean_dec(v_x_3051_);
    return v_res_3052_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(
    mut v_x_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_a_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3057_) == 0 {
                    v___x_3058_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_3058_;
                } else {
                    v___x_3059_ = l_Lean_Json_getBool_x3f(v_x_3057_);
                    if crate::leanh::lean_obj_tag(v___x_3059_) == 0 {
                        v_a_3060_ = crate::leanh::lean_ctor_get(v___x_3059_, 0);
                        v_isSharedCheck_3067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3059_)) as u8;
                        if v_isSharedCheck_3067_ == 0 {
                            v___x_3062_ = v___x_3059_;
                            v_isShared_3063_ = v_isSharedCheck_3067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3060_);
                            crate::leanh::lean_dec(v___x_3059_);
                            v___x_3062_ = crate::leanh::lean_box(0);
                            v_isShared_3063_ = v_isSharedCheck_3067_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3068_ = crate::leanh::lean_ctor_get(v___x_3059_, 0);
                        v_isSharedCheck_3076_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3059_)) as u8;
                        if v_isSharedCheck_3076_ == 0 {
                            v___x_3070_ = v___x_3059_;
                            v_isShared_3071_ = v_isSharedCheck_3076_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3068_);
                            crate::leanh::lean_dec(v___x_3059_);
                            v___x_3070_ = crate::leanh::lean_box(0);
                            v_isShared_3071_ = v_isSharedCheck_3076_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3063_ == 0 {
                    v___x_3065_ = v___x_3062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
                    v___x_3065_ = v_reuseFailAlloc_3066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3065_;
            }
            3 => {
                v___x_3072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3072_, 0, v_a_3068_);
                if v_isShared_3071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3070_, 0, v___x_3072_);
                    v___x_3074_ = v___x_3070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
                    v___x_3074_ = v_reuseFailAlloc_3075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___boxed(
    mut v_x_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3078_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(v_x_3077_);
    crate::leanh::lean_dec(v_x_3077_);
    return v_res_3078_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(
    mut v_j_3079_: *mut crate::leanh::LeanObject,
    mut v_k_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3081_ = l_Lean_Json_getObjValD(v_j_3079_, v_k_3080_);
    v___x_3082_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(v___x_3081_);
    crate::leanh::lean_dec(v___x_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0___boxed(
    mut v_j_3083_: *mut crate::leanh::LeanObject,
    mut v_k_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_j_3083_, v_k_3084_);
    crate::leanh::lean_dec_ref(v_k_3084_);
    return v_res_3085_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = 1;
    v___x_3094_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3;
    v___x_3095_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3094_, v___x_3093_);
    return v___x_3095_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3097_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4,
    );
    v___x_3099_ = lean_string_append(v___x_3098_, v___x_3097_);
    return v___x_3099_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3103_ = 1;
    v___x_3104_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8;
    v___x_3105_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3104_, v___x_3103_);
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9,
    );
    v___x_3107_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6,
    );
    v___x_3108_ = lean_string_append(v___x_3107_, v___x_3106_);
    return v___x_3108_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3111_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10,
    );
    v___x_3112_ = lean_string_append(v___x_3111_, v___x_3110_);
    return v___x_3112_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson(
    mut v_json_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_a_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut v_a_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3114_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0;
                v___x_3115_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_3113_, v___x_3114_);
                if crate::leanh::lean_obj_tag(v___x_3115_) == 0 {
                    v_a_3116_ = crate::leanh::lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3125_ = (!crate::leanh::lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3125_ == 0 {
                        v___x_3118_ = v___x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3116_);
                        crate::leanh::lean_dec(v___x_3115_);
                        v___x_3118_ = crate::leanh::lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3125_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3115_) == 0 {
                        v_a_3126_ = crate::leanh::lean_ctor_get(v___x_3115_, 0);
                        v_isSharedCheck_3133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3115_)) as u8;
                        if v_isSharedCheck_3133_ == 0 {
                            v___x_3128_ = v___x_3115_;
                            v_isShared_3129_ = v_isSharedCheck_3133_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3126_);
                            crate::leanh::lean_dec(v___x_3115_);
                            v___x_3128_ = crate::leanh::lean_box(0);
                            v_isShared_3129_ = v_isSharedCheck_3133_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3134_ = crate::leanh::lean_ctor_get(v___x_3115_, 0);
                        v_isSharedCheck_3141_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3115_)) as u8;
                        if v_isSharedCheck_3141_ == 0 {
                            v___x_3136_ = v___x_3115_;
                            v_isShared_3137_ = v_isSharedCheck_3141_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3134_);
                            crate::leanh::lean_dec(v___x_3115_);
                            v___x_3136_ = crate::leanh::lean_box(0);
                            v_isShared_3137_ = v_isSharedCheck_3141_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3120_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12_once), _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12);
                v___x_3121_ = lean_string_append(v___x_3120_, v_a_3116_);
                crate::leanh::lean_dec(v_a_3116_);
                if v_isShared_3119_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3118_, 0, v___x_3121_);
                    v___x_3123_ = v___x_3118_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3123_;
            }
            3 => {
                if v_isShared_3129_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3128_, 0);
                    v___x_3131_ = v___x_3128_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
                    v___x_3131_ = v_reuseFailAlloc_3132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3131_;
            }
            5 => {
                if v_isShared_3137_ == 0 {
                    v___x_3139_ = v___x_3136_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
                    v___x_3139_ = v_reuseFailAlloc_3140_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(
    mut v_k_3144_: *mut crate::leanh::LeanObject,
    mut v_x_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3145_) == 0 {
        let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3144_);
        v___x_3146_ = crate::leanh::lean_box(0);
        return v___x_3146_;
    } else {
        let mut v_val_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3147_ = crate::leanh::lean_ctor_get(v_x_3145_, 0);
        v___x_3148_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(v_val_3147_);
        v___x_3149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3149_, 0, v_k_3144_);
        crate::leanh::lean_ctor_set(v___x_3149_, 1, v___x_3148_);
        v___x_3150_ = crate::leanh::lean_box(0);
        v___x_3151_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3151_, 0, v___x_3149_);
        crate::leanh::lean_ctor_set(v___x_3151_, 1, v___x_3150_);
        return v___x_3151_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0___boxed(
    mut v_k_3152_: *mut crate::leanh::LeanObject,
    mut v_x_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(
            v_k_3152_, v_x_3153_,
        );
    crate::leanh::lean_dec(v_x_3153_);
    return v_res_3154_;
}
pub unsafe fn l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(
    mut v_x_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3157_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0;
    v___x_3158_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(
            v___x_3157_,
            v_x_3156_,
        );
    v___x_3159_ = crate::leanh::lean_box(0);
    v___x_3160_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3160_, 0, v___x_3158_);
    crate::leanh::lean_ctor_set(v___x_3160_, 1, v___x_3159_);
    v___x_3161_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3162_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3160_, v___x_3161_);
    v___x_3163_ = l_Lean_Json_mkObj(v___x_3162_);
    crate::leanh::lean_dec(v___x_3162_);
    return v___x_3163_;
}
pub unsafe fn l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___boxed(
    mut v_x_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3165_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(v_x_3164_);
    crate::leanh::lean_dec(v_x_3164_);
    return v_res_3165_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_3170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v_a_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3184_: u8 = 0;
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3170_) == 0 {
                    v___x_3171_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_3171_;
                } else {
                    v___x_3172_ =
                        l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson(v_x_3170_);
                    if crate::leanh::lean_obj_tag(v___x_3172_) == 0 {
                        v_a_3173_ = crate::leanh::lean_ctor_get(v___x_3172_, 0);
                        v_isSharedCheck_3180_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3172_)) as u8;
                        if v_isSharedCheck_3180_ == 0 {
                            v___x_3175_ = v___x_3172_;
                            v_isShared_3176_ = v_isSharedCheck_3180_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3173_);
                            crate::leanh::lean_dec(v___x_3172_);
                            v___x_3175_ = crate::leanh::lean_box(0);
                            v_isShared_3176_ = v_isSharedCheck_3180_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3181_ = crate::leanh::lean_ctor_get(v___x_3172_, 0);
                        v_isSharedCheck_3189_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3172_)) as u8;
                        if v_isSharedCheck_3189_ == 0 {
                            v___x_3183_ = v___x_3172_;
                            v_isShared_3184_ = v_isSharedCheck_3189_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3181_);
                            crate::leanh::lean_dec(v___x_3172_);
                            v___x_3183_ = crate::leanh::lean_box(0);
                            v_isShared_3184_ = v_isSharedCheck_3189_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3176_ == 0 {
                    v___x_3178_ = v___x_3175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
                    v___x_3178_ = v_reuseFailAlloc_3179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3178_;
            }
            3 => {
                v___x_3185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3185_, 0, v_a_3181_);
                if v_isShared_3184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3183_, 0, v___x_3185_);
                    v___x_3187_ = v___x_3183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
                    v___x_3187_ = v_reuseFailAlloc_3188_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(
    mut v_j_3190_: *mut crate::leanh::LeanObject,
    mut v_k_3191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = l_Lean_Json_getObjValD(v_j_3190_, v_k_3191_);
    v___x_3193_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(v___x_3192_);
    return v___x_3193_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_3194_: *mut crate::leanh::LeanObject,
    mut v_k_3195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(v_j_3194_, v_k_3195_);
    crate::leanh::lean_dec_ref(v_k_3195_);
    return v_res_3196_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = 1;
    v___x_3203_ = l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1;
    v___x_3204_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3203_, v___x_3202_);
    return v___x_3204_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2,
    );
    v___x_3207_ = lean_string_append(v___x_3206_, v___x_3205_);
    return v___x_3207_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3211_ = 1;
    v___x_3212_ = l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5;
    v___x_3213_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3212_, v___x_3211_);
    return v___x_3213_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6,
    );
    v___x_3215_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3,
    );
    v___x_3216_ = lean_string_append(v___x_3215_, v___x_3214_);
    return v___x_3216_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3218_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7,
    );
    v___x_3219_ = lean_string_append(v___x_3218_, v___x_3217_);
    return v___x_3219_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(
    mut v_json_3220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v_a_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3221_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0;
                v___x_3222_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(v_json_3220_, v___x_3221_);
                if crate::leanh::lean_obj_tag(v___x_3222_) == 0 {
                    v_a_3223_ = crate::leanh::lean_ctor_get(v___x_3222_, 0);
                    v_isSharedCheck_3232_ = (!crate::leanh::lean_is_exclusive(v___x_3222_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3225_ = v___x_3222_;
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3223_);
                        crate::leanh::lean_dec(v___x_3222_);
                        v___x_3225_ = crate::leanh::lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3222_) == 0 {
                        v_a_3233_ = crate::leanh::lean_ctor_get(v___x_3222_, 0);
                        v_isSharedCheck_3240_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3222_)) as u8;
                        if v_isSharedCheck_3240_ == 0 {
                            v___x_3235_ = v___x_3222_;
                            v_isShared_3236_ = v_isSharedCheck_3240_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3233_);
                            crate::leanh::lean_dec(v___x_3222_);
                            v___x_3235_ = crate::leanh::lean_box(0);
                            v_isShared_3236_ = v_isSharedCheck_3240_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3241_ = crate::leanh::lean_ctor_get(v___x_3222_, 0);
                        v_isSharedCheck_3248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3222_)) as u8;
                        if v_isSharedCheck_3248_ == 0 {
                            v___x_3243_ = v___x_3222_;
                            v_isShared_3244_ = v_isSharedCheck_3248_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3241_);
                            crate::leanh::lean_dec(v___x_3222_);
                            v___x_3243_ = crate::leanh::lean_box(0);
                            v_isShared_3244_ = v_isSharedCheck_3248_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3227_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8);
                v___x_3228_ = lean_string_append(v___x_3227_, v_a_3223_);
                crate::leanh::lean_dec(v_a_3223_);
                if v_isShared_3226_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3225_, 0, v___x_3228_);
                    v___x_3230_ = v___x_3225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3230_;
            }
            3 => {
                if v_isShared_3236_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3235_, 0);
                    v___x_3238_ = v___x_3235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3238_;
            }
            5 => {
                if v_isShared_3244_ == 0 {
                    v___x_3246_ = v___x_3243_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(
    mut v_k_3251_: *mut crate::leanh::LeanObject,
    mut v_x_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3252_) == 0 {
        let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3251_);
        v___x_3253_ = crate::leanh::lean_box(0);
        return v___x_3253_;
    } else {
        let mut v_val_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3254_ = crate::leanh::lean_ctor_get(v_x_3252_, 0);
        v___x_3255_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(v_val_3254_);
        v___x_3256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3256_, 0, v_k_3251_);
        crate::leanh::lean_ctor_set(v___x_3256_, 1, v___x_3255_);
        v___x_3257_ = crate::leanh::lean_box(0);
        v___x_3258_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3258_, 0, v___x_3256_);
        crate::leanh::lean_ctor_set(v___x_3258_, 1, v___x_3257_);
        return v___x_3258_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0___boxed(
    mut v_k_3259_: *mut crate::leanh::LeanObject,
    mut v_x_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3261_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(
            v_k_3259_, v_x_3260_,
        );
    crate::leanh::lean_dec(v_x_3260_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(
    mut v_k_3262_: *mut crate::leanh::LeanObject,
    mut v_x_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3263_) == 0 {
        let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3262_);
        v___x_3264_ = crate::leanh::lean_box(0);
        return v___x_3264_;
    } else {
        let mut v_val_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3265_ = crate::leanh::lean_ctor_get(v_x_3263_, 0);
        crate::leanh::lean_inc(v_val_3265_);
        crate::leanh::lean_dec_ref_known(v_x_3263_, 1);
        v___x_3266_ = l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson(v_val_3265_);
        v___x_3267_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3267_, 0, v_k_3262_);
        crate::leanh::lean_ctor_set(v___x_3267_, 1, v___x_3266_);
        v___x_3268_ = crate::leanh::lean_box(0);
        v___x_3269_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3267_);
        crate::leanh::lean_ctor_set(v___x_3269_, 1, v___x_3268_);
        return v___x_3269_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(
    mut v_k_3270_: *mut crate::leanh::LeanObject,
    mut v_x_3271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3271_) == 0 {
        let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3270_);
        v___x_3272_ = crate::leanh::lean_box(0);
        return v___x_3272_;
    } else {
        let mut v_val_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3273_ = crate::leanh::lean_ctor_get(v_x_3271_, 0);
        crate::leanh::lean_inc(v_val_3273_);
        crate::leanh::lean_dec_ref_known(v_x_3271_, 1);
        v___x_3274_ = l_Lean_Lsp_instToJsonInlayHintClientCapabilities_toJson(v_val_3273_);
        v___x_3275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3275_, 0, v_k_3270_);
        crate::leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
        v___x_3276_ = crate::leanh::lean_box(0);
        v___x_3277_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3277_, 0, v___x_3275_);
        crate::leanh::lean_ctor_set(v___x_3277_, 1, v___x_3276_);
        return v___x_3277_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(
    mut v_x_3281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_completion_x3f_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_codeAction_x3f_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlayHint_x3f_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_completion_x3f_3282_ = crate::leanh::lean_ctor_get(v_x_3281_, 0);
    crate::leanh::lean_inc(v_completion_x3f_3282_);
    v_codeAction_x3f_3283_ = crate::leanh::lean_ctor_get(v_x_3281_, 1);
    crate::leanh::lean_inc(v_codeAction_x3f_3283_);
    v_inlayHint_x3f_3284_ = crate::leanh::lean_ctor_get(v_x_3281_, 2);
    crate::leanh::lean_inc(v_inlayHint_x3f_3284_);
    crate::leanh::lean_dec_ref(v_x_3281_);
    v___x_3285_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0;
    v___x_3286_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(
            v___x_3285_,
            v_completion_x3f_3282_,
        );
    crate::leanh::lean_dec(v_completion_x3f_3282_);
    v___x_3287_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1;
    v___x_3288_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(
            v___x_3287_,
            v_codeAction_x3f_3283_,
        );
    v___x_3289_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2;
    v___x_3290_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(
            v___x_3289_,
            v_inlayHint_x3f_3284_,
        );
    v___x_3291_ = crate::leanh::lean_box(0);
    v___x_3292_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3292_, 0, v___x_3290_);
    crate::leanh::lean_ctor_set(v___x_3292_, 1, v___x_3291_);
    v___x_3293_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3293_, 0, v___x_3288_);
    crate::leanh::lean_ctor_set(v___x_3293_, 1, v___x_3292_);
    v___x_3294_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3286_);
    crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
    v___x_3295_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3296_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3294_, v___x_3295_);
    v___x_3297_ = l_Lean_Json_mkObj(v___x_3296_);
    crate::leanh::lean_dec(v___x_3296_);
    return v___x_3297_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(
    mut v_x_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut v_a_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3302_) == 0 {
                    v___x_3303_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0;
                    return v___x_3303_;
                } else {
                    v___x_3304_ =
                        l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson(v_x_3302_);
                    if crate::leanh::lean_obj_tag(v___x_3304_) == 0 {
                        v_a_3305_ = crate::leanh::lean_ctor_get(v___x_3304_, 0);
                        v_isSharedCheck_3312_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3304_)) as u8;
                        if v_isSharedCheck_3312_ == 0 {
                            v___x_3307_ = v___x_3304_;
                            v_isShared_3308_ = v_isSharedCheck_3312_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3305_);
                            crate::leanh::lean_dec(v___x_3304_);
                            v___x_3307_ = crate::leanh::lean_box(0);
                            v_isShared_3308_ = v_isSharedCheck_3312_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3313_ = crate::leanh::lean_ctor_get(v___x_3304_, 0);
                        v_isSharedCheck_3321_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3304_)) as u8;
                        if v_isSharedCheck_3321_ == 0 {
                            v___x_3315_ = v___x_3304_;
                            v_isShared_3316_ = v_isSharedCheck_3321_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3313_);
                            crate::leanh::lean_dec(v___x_3304_);
                            v___x_3315_ = crate::leanh::lean_box(0);
                            v_isShared_3316_ = v_isSharedCheck_3321_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3308_ == 0 {
                    v___x_3310_ = v___x_3307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
                    v___x_3310_ = v_reuseFailAlloc_3311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3310_;
            }
            3 => {
                v___x_3317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3317_, 0, v_a_3313_);
                if v_isShared_3316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3315_, 0, v___x_3317_);
                    v___x_3319_ = v___x_3315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(
    mut v_j_3322_: *mut crate::leanh::LeanObject,
    mut v_k_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Lean_Json_getObjValD(v_j_3322_, v_k_3323_);
    v___x_3325_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(v___x_3324_);
    return v___x_3325_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1___boxed(
    mut v_j_3326_: *mut crate::leanh::LeanObject,
    mut v_k_3327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(v_j_3326_, v_k_3327_);
    crate::leanh::lean_dec_ref(v_k_3327_);
    return v_res_3328_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_3331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut v_a_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3345_: u8 = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3331_) == 0 {
                    v___x_3332_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_3332_;
                } else {
                    v___x_3333_ =
                        l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(v_x_3331_);
                    if crate::leanh::lean_obj_tag(v___x_3333_) == 0 {
                        v_a_3334_ = crate::leanh::lean_ctor_get(v___x_3333_, 0);
                        v_isSharedCheck_3341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3333_)) as u8;
                        if v_isSharedCheck_3341_ == 0 {
                            v___x_3336_ = v___x_3333_;
                            v_isShared_3337_ = v_isSharedCheck_3341_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3334_);
                            crate::leanh::lean_dec(v___x_3333_);
                            v___x_3336_ = crate::leanh::lean_box(0);
                            v_isShared_3337_ = v_isSharedCheck_3341_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3342_ = crate::leanh::lean_ctor_get(v___x_3333_, 0);
                        v_isSharedCheck_3350_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3333_)) as u8;
                        if v_isSharedCheck_3350_ == 0 {
                            v___x_3344_ = v___x_3333_;
                            v_isShared_3345_ = v_isSharedCheck_3350_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3342_);
                            crate::leanh::lean_dec(v___x_3333_);
                            v___x_3344_ = crate::leanh::lean_box(0);
                            v_isShared_3345_ = v_isSharedCheck_3350_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3337_ == 0 {
                    v___x_3339_ = v___x_3336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
                    v___x_3339_ = v_reuseFailAlloc_3340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3339_;
            }
            3 => {
                v___x_3346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3346_, 0, v_a_3342_);
                if v_isShared_3345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3346_);
                    v___x_3348_ = v___x_3344_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(
    mut v_j_3351_: *mut crate::leanh::LeanObject,
    mut v_k_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3353_ = l_Lean_Json_getObjValD(v_j_3351_, v_k_3352_);
    v___x_3354_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(v___x_3353_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_3355_: *mut crate::leanh::LeanObject,
    mut v_k_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(v_j_3355_, v_k_3356_);
    crate::leanh::lean_dec_ref(v_k_3356_);
    return v_res_3357_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(
    mut v_x_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v_a_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3360_) == 0 {
                    v___x_3361_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0;
                    return v___x_3361_;
                } else {
                    v___x_3362_ =
                        l_Lean_Lsp_instFromJsonInlayHintClientCapabilities_fromJson(v_x_3360_);
                    if crate::leanh::lean_obj_tag(v___x_3362_) == 0 {
                        v_a_3363_ = crate::leanh::lean_ctor_get(v___x_3362_, 0);
                        v_isSharedCheck_3370_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3362_)) as u8;
                        if v_isSharedCheck_3370_ == 0 {
                            v___x_3365_ = v___x_3362_;
                            v_isShared_3366_ = v_isSharedCheck_3370_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3363_);
                            crate::leanh::lean_dec(v___x_3362_);
                            v___x_3365_ = crate::leanh::lean_box(0);
                            v_isShared_3366_ = v_isSharedCheck_3370_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3371_ = crate::leanh::lean_ctor_get(v___x_3362_, 0);
                        v_isSharedCheck_3379_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3362_)) as u8;
                        if v_isSharedCheck_3379_ == 0 {
                            v___x_3373_ = v___x_3362_;
                            v_isShared_3374_ = v_isSharedCheck_3379_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3371_);
                            crate::leanh::lean_dec(v___x_3362_);
                            v___x_3373_ = crate::leanh::lean_box(0);
                            v_isShared_3374_ = v_isSharedCheck_3379_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3366_ == 0 {
                    v___x_3368_ = v___x_3365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
                    v___x_3368_ = v_reuseFailAlloc_3369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3368_;
            }
            3 => {
                v___x_3375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3375_, 0, v_a_3371_);
                if v_isShared_3374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v___x_3375_);
                    v___x_3377_ = v___x_3373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
                    v___x_3377_ = v_reuseFailAlloc_3378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(
    mut v_j_3380_: *mut crate::leanh::LeanObject,
    mut v_k_3381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3382_ = l_Lean_Json_getObjValD(v_j_3380_, v_k_3381_);
    v___x_3383_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(v___x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2___boxed(
    mut v_j_3384_: *mut crate::leanh::LeanObject,
    mut v_k_3385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(v_j_3384_, v_k_3385_);
    crate::leanh::lean_dec_ref(v_k_3385_);
    return v_res_3386_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = 1;
    v___x_3393_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1;
    v___x_3394_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3393_, v___x_3392_);
    return v___x_3394_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3396_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2,
    );
    v___x_3397_ = lean_string_append(v___x_3396_, v___x_3395_);
    return v___x_3397_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = 1;
    v___x_3402_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5;
    v___x_3403_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3402_, v___x_3401_);
    return v___x_3403_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6,
    );
    v___x_3405_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3,
    );
    v___x_3406_ = lean_string_append(v___x_3405_, v___x_3404_);
    return v___x_3406_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3408_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7,
    );
    v___x_3409_ = lean_string_append(v___x_3408_, v___x_3407_);
    return v___x_3409_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3413_: u8 = 0;
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3413_ = 1;
    v___x_3414_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10;
    v___x_3415_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3414_, v___x_3413_);
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11,
    );
    v___x_3417_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3,
    );
    v___x_3418_ = lean_string_append(v___x_3417_, v___x_3416_);
    return v___x_3418_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3419_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3420_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12,
    );
    v___x_3421_ = lean_string_append(v___x_3420_, v___x_3419_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3425_: u8 = 0;
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = 1;
    v___x_3426_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15;
    v___x_3427_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3426_, v___x_3425_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16,
    );
    v___x_3429_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3,
    );
    v___x_3430_ = lean_string_append(v___x_3429_, v___x_3428_);
    return v___x_3430_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17,
    );
    v___x_3433_ = lean_string_append(v___x_3432_, v___x_3431_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(
    mut v_json_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_a_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v_a_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut v_a_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3482_: u8 = 0;
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_a_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_a_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3435_ =
                    l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0;
                crate::leanh::lean_inc(v_json_3434_);
                v___x_3436_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(v_json_3434_, v___x_3435_);
                if crate::leanh::lean_obj_tag(v___x_3436_) == 0 {
                    crate::leanh::lean_dec(v_json_3434_);
                    v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3446_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3446_ == 0 {
                        v___x_3439_ = v___x_3436_;
                        v_isShared_3440_ = v_isSharedCheck_3446_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3437_);
                        crate::leanh::lean_dec(v___x_3436_);
                        v___x_3439_ = crate::leanh::lean_box(0);
                        v_isShared_3440_ = v_isSharedCheck_3446_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3436_) == 0 {
                        crate::leanh::lean_dec(v_json_3434_);
                        v_a_3447_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                        v_isSharedCheck_3454_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                        if v_isSharedCheck_3454_ == 0 {
                            v___x_3449_ = v___x_3436_;
                            v_isShared_3450_ = v_isSharedCheck_3454_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3447_);
                            crate::leanh::lean_dec(v___x_3436_);
                            v___x_3449_ = crate::leanh::lean_box(0);
                            v_isShared_3450_ = v_isSharedCheck_3454_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3455_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                        crate::leanh::lean_inc(v_a_3455_);
                        crate::leanh::lean_dec_ref_known(v___x_3436_, 1);
                        v___x_3456_ =
                            l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_3434_);
                        v___x_3457_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(v_json_3434_, v___x_3456_);
                        if crate::leanh::lean_obj_tag(v___x_3457_) == 0 {
                            crate::leanh::lean_dec(v_a_3455_);
                            crate::leanh::lean_dec(v_json_3434_);
                            v_a_3458_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                            v_isSharedCheck_3467_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3457_)) as u8;
                            if v_isSharedCheck_3467_ == 0 {
                                v___x_3460_ = v___x_3457_;
                                v_isShared_3461_ = v_isSharedCheck_3467_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3458_);
                                crate::leanh::lean_dec(v___x_3457_);
                                v___x_3460_ = crate::leanh::lean_box(0);
                                v_isShared_3461_ = v_isSharedCheck_3467_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3457_) == 0 {
                                crate::leanh::lean_dec(v_a_3455_);
                                crate::leanh::lean_dec(v_json_3434_);
                                v_a_3468_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                                v_isSharedCheck_3475_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3457_)) as u8;
                                if v_isSharedCheck_3475_ == 0 {
                                    v___x_3470_ = v___x_3457_;
                                    v_isShared_3471_ = v_isSharedCheck_3475_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3468_);
                                    crate::leanh::lean_dec(v___x_3457_);
                                    v___x_3470_ = crate::leanh::lean_box(0);
                                    v_isShared_3471_ = v_isSharedCheck_3475_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3476_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                                crate::leanh::lean_inc(v_a_3476_);
                                crate::leanh::lean_dec_ref_known(v___x_3457_, 1);
                                v___x_3477_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2;
                                v___x_3478_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(v_json_3434_, v___x_3477_);
                                if crate::leanh::lean_obj_tag(v___x_3478_) == 0 {
                                    crate::leanh::lean_dec(v_a_3476_);
                                    crate::leanh::lean_dec(v_a_3455_);
                                    v_a_3479_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                                    v_isSharedCheck_3488_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3478_)) as u8;
                                    if v_isSharedCheck_3488_ == 0 {
                                        v___x_3481_ = v___x_3478_;
                                        v_isShared_3482_ = v_isSharedCheck_3488_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3479_);
                                        crate::leanh::lean_dec(v___x_3478_);
                                        v___x_3481_ = crate::leanh::lean_box(0);
                                        v_isShared_3482_ = v_isSharedCheck_3488_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_3478_) == 0 {
                                        crate::leanh::lean_dec(v_a_3476_);
                                        crate::leanh::lean_dec(v_a_3455_);
                                        v_a_3489_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                                        v_isSharedCheck_3496_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3478_)) as u8;
                                        if v_isSharedCheck_3496_ == 0 {
                                            v___x_3491_ = v___x_3478_;
                                            v_isShared_3492_ = v_isSharedCheck_3496_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3489_);
                                            crate::leanh::lean_dec(v___x_3478_);
                                            v___x_3491_ = crate::leanh::lean_box(0);
                                            v_isShared_3492_ = v_isSharedCheck_3496_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_3497_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                                        v_isSharedCheck_3505_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3478_)) as u8;
                                        if v_isSharedCheck_3505_ == 0 {
                                            v___x_3499_ = v___x_3478_;
                                            v_isShared_3500_ = v_isSharedCheck_3505_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3497_);
                                            crate::leanh::lean_dec(v___x_3478_);
                                            v___x_3499_ = crate::leanh::lean_box(0);
                                            v_isShared_3500_ = v_isSharedCheck_3505_;
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
                v___x_3441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8);
                v___x_3442_ = lean_string_append(v___x_3441_, v_a_3437_);
                crate::leanh::lean_dec(v_a_3437_);
                if v_isShared_3440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3444_;
            }
            3 => {
                if v_isShared_3450_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3449_, 0);
                    v___x_3452_ = v___x_3449_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3452_;
            }
            5 => {
                v___x_3462_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13_once), _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13);
                v___x_3463_ = lean_string_append(v___x_3462_, v_a_3458_);
                crate::leanh::lean_dec(v_a_3458_);
                if v_isShared_3461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3460_, 0, v___x_3463_);
                    v___x_3465_ = v___x_3460_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
                    v___x_3465_ = v_reuseFailAlloc_3466_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3465_;
            }
            7 => {
                if v_isShared_3471_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3470_, 0);
                    v___x_3473_ = v___x_3470_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
                    v___x_3473_ = v_reuseFailAlloc_3474_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3473_;
            }
            9 => {
                v___x_3483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18_once), _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18);
                v___x_3484_ = lean_string_append(v___x_3483_, v_a_3479_);
                crate::leanh::lean_dec(v_a_3479_);
                if v_isShared_3482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3481_, 0, v___x_3484_);
                    v___x_3486_ = v___x_3481_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
                    v___x_3486_ = v_reuseFailAlloc_3487_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3486_;
            }
            11 => {
                if v_isShared_3492_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3491_, 0);
                    v___x_3494_ = v___x_3491_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
                    v___x_3494_ = v_reuseFailAlloc_3495_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3494_;
            }
            13 => {
                v___x_3501_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3501_, 0, v_a_3455_);
                crate::leanh::lean_ctor_set(v___x_3501_, 1, v_a_3476_);
                crate::leanh::lean_ctor_set(v___x_3501_, 2, v_a_3497_);
                if v_isShared_3500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3499_, 0, v___x_3501_);
                    v___x_3503_ = v___x_3499_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
                    v___x_3503_ = v_reuseFailAlloc_3504_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(
    mut v_x_3509_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3510_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0;
    v___x_3511_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_3511_, 0 as u32, v_x_3509_);
    v___x_3512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3512_, 0, v___x_3510_);
    crate::leanh::lean_ctor_set(v___x_3512_, 1, v___x_3511_);
    v___x_3513_ = crate::leanh::lean_box(0);
    v___x_3514_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3514_, 0, v___x_3512_);
    crate::leanh::lean_ctor_set(v___x_3514_, 1, v___x_3513_);
    v___x_3515_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3514_);
    crate::leanh::lean_ctor_set(v___x_3515_, 1, v___x_3513_);
    v___x_3516_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3517_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3515_, v___x_3516_);
    v___x_3518_ = l_Lean_Json_mkObj(v___x_3517_);
    crate::leanh::lean_dec(v___x_3517_);
    return v___x_3518_;
}
pub unsafe fn l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed(
    mut v_x_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_29__boxed_3520_: u8 = 0;
    let mut v_res_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_29__boxed_3520_ = (crate::leanh::lean_unbox(v_x_3519_) as u8);
    v_res_3521_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v_x_29__boxed_3520_);
    return v_res_3521_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(
    mut v_j_3524_: *mut crate::leanh::LeanObject,
    mut v_k_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_Json_getObjValD(v_j_3524_, v_k_3525_);
    v___x_3527_ = l_Lean_Json_getBool_x3f(v___x_3526_);
    crate::leanh::lean_dec(v___x_3526_);
    return v___x_3527_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_3528_: *mut crate::leanh::LeanObject,
    mut v_k_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3530_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_j_3528_, v_k_3529_);
    crate::leanh::lean_dec_ref(v_k_3529_);
    return v_res_3530_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3536_ = 1;
    v___x_3537_ = l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1;
    v___x_3538_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3537_, v___x_3536_);
    return v___x_3538_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2,
    );
    v___x_3541_ = lean_string_append(v___x_3540_, v___x_3539_);
    return v___x_3541_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3544_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3544_ = 1;
    v___x_3545_ = l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4;
    v___x_3546_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3545_, v___x_3544_);
    return v___x_3546_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5,
    );
    v___x_3548_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3,
    );
    v___x_3549_ = lean_string_append(v___x_3548_, v___x_3547_);
    return v___x_3549_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3551_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6,
    );
    v___x_3552_ = lean_string_append(v___x_3551_, v___x_3550_);
    return v___x_3552_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(
    mut v_json_3553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3565_: u8 = 0;
    let mut v_a_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3573_: u8 = 0;
    let mut v_a_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3554_ =
                    l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0;
                v___x_3555_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_3553_, v___x_3554_);
                if crate::leanh::lean_obj_tag(v___x_3555_) == 0 {
                    v_a_3556_ = crate::leanh::lean_ctor_get(v___x_3555_, 0);
                    v_isSharedCheck_3565_ = (!crate::leanh::lean_is_exclusive(v___x_3555_)) as u8;
                    if v_isSharedCheck_3565_ == 0 {
                        v___x_3558_ = v___x_3555_;
                        v_isShared_3559_ = v_isSharedCheck_3565_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3556_);
                        crate::leanh::lean_dec(v___x_3555_);
                        v___x_3558_ = crate::leanh::lean_box(0);
                        v_isShared_3559_ = v_isSharedCheck_3565_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3555_) == 0 {
                        v_a_3566_ = crate::leanh::lean_ctor_get(v___x_3555_, 0);
                        v_isSharedCheck_3573_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3555_)) as u8;
                        if v_isSharedCheck_3573_ == 0 {
                            v___x_3568_ = v___x_3555_;
                            v_isShared_3569_ = v_isSharedCheck_3573_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3566_);
                            crate::leanh::lean_dec(v___x_3555_);
                            v___x_3568_ = crate::leanh::lean_box(0);
                            v_isShared_3569_ = v_isSharedCheck_3573_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3574_ = crate::leanh::lean_ctor_get(v___x_3555_, 0);
                        v_isSharedCheck_3581_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3555_)) as u8;
                        if v_isSharedCheck_3581_ == 0 {
                            v___x_3576_ = v___x_3555_;
                            v_isShared_3577_ = v_isSharedCheck_3581_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3574_);
                            crate::leanh::lean_dec(v___x_3555_);
                            v___x_3576_ = crate::leanh::lean_box(0);
                            v_isShared_3577_ = v_isSharedCheck_3581_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7_once), _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7);
                v___x_3561_ = lean_string_append(v___x_3560_, v_a_3556_);
                crate::leanh::lean_dec(v_a_3556_);
                if v_isShared_3559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3558_, 0, v___x_3561_);
                    v___x_3563_ = v___x_3558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
                    v___x_3563_ = v_reuseFailAlloc_3564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3563_;
            }
            3 => {
                if v_isShared_3569_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3568_, 0);
                    v___x_3571_ = v___x_3568_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
                    v___x_3571_ = v_reuseFailAlloc_3572_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3571_;
            }
            5 => {
                if v_isShared_3577_ == 0 {
                    v___x_3579_ = v___x_3576_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
                    v___x_3579_ = v_reuseFailAlloc_3580_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(
    mut v_k_3584_: *mut crate::leanh::LeanObject,
    mut v_x_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3585_) == 0 {
        let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3584_);
        v___x_3586_ = crate::leanh::lean_box(0);
        return v___x_3586_;
    } else {
        let mut v_val_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3588_: u8 = 0;
        let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3587_ = crate::leanh::lean_ctor_get(v_x_3585_, 0);
        v___x_3588_ = (crate::leanh::lean_unbox(v_val_3587_) as u8);
        v___x_3589_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v___x_3588_);
        v___x_3590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3590_, 0, v_k_3584_);
        crate::leanh::lean_ctor_set(v___x_3590_, 1, v___x_3589_);
        v___x_3591_ = crate::leanh::lean_box(0);
        v___x_3592_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3592_, 0, v___x_3590_);
        crate::leanh::lean_ctor_set(v___x_3592_, 1, v___x_3591_);
        return v___x_3592_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0___boxed(
    mut v_k_3593_: *mut crate::leanh::LeanObject,
    mut v_x_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3595_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(
            v_k_3593_, v_x_3594_,
        );
    crate::leanh::lean_dec(v_x_3594_);
    return v_res_3595_;
}
pub unsafe fn l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(
    mut v_x_3597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0;
    v___x_3599_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(
            v___x_3598_,
            v_x_3597_,
        );
    v___x_3600_ = crate::leanh::lean_box(0);
    v___x_3601_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3601_, 0, v___x_3599_);
    crate::leanh::lean_ctor_set(v___x_3601_, 1, v___x_3600_);
    v___x_3602_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3603_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3601_, v___x_3602_);
    v___x_3604_ = l_Lean_Json_mkObj(v___x_3603_);
    crate::leanh::lean_dec(v___x_3603_);
    return v___x_3604_;
}
pub unsafe fn l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed(
    mut v_x_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3606_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_x_3605_);
    crate::leanh::lean_dec(v_x_3605_);
    return v_res_3606_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3619_: u8 = 0;
    let mut v_a_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3609_) == 0 {
                    v___x_3610_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_3610_;
                } else {
                    v___x_3611_ =
                        l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(v_x_3609_);
                    if crate::leanh::lean_obj_tag(v___x_3611_) == 0 {
                        v_a_3612_ = crate::leanh::lean_ctor_get(v___x_3611_, 0);
                        v_isSharedCheck_3619_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3611_)) as u8;
                        if v_isSharedCheck_3619_ == 0 {
                            v___x_3614_ = v___x_3611_;
                            v_isShared_3615_ = v_isSharedCheck_3619_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3612_);
                            crate::leanh::lean_dec(v___x_3611_);
                            v___x_3614_ = crate::leanh::lean_box(0);
                            v_isShared_3615_ = v_isSharedCheck_3619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3620_ = crate::leanh::lean_ctor_get(v___x_3611_, 0);
                        v_isSharedCheck_3628_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3611_)) as u8;
                        if v_isSharedCheck_3628_ == 0 {
                            v___x_3622_ = v___x_3611_;
                            v_isShared_3623_ = v_isSharedCheck_3628_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3620_);
                            crate::leanh::lean_dec(v___x_3611_);
                            v___x_3622_ = crate::leanh::lean_box(0);
                            v_isShared_3623_ = v_isSharedCheck_3628_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3615_ == 0 {
                    v___x_3617_ = v___x_3614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
                    v___x_3617_ = v_reuseFailAlloc_3618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3617_;
            }
            3 => {
                v___x_3624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3624_, 0, v_a_3620_);
                if v_isShared_3623_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3622_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(
    mut v_j_3629_: *mut crate::leanh::LeanObject,
    mut v_k_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = l_Lean_Json_getObjValD(v_j_3629_, v_k_3630_);
    v___x_3632_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(v___x_3631_);
    return v___x_3632_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_3633_: *mut crate::leanh::LeanObject,
    mut v_k_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3635_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_j_3633_, v_k_3634_);
    crate::leanh::lean_dec_ref(v_k_3634_);
    return v_res_3635_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3641_ = 1;
    v___x_3642_ = l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1;
    v___x_3643_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3642_, v___x_3641_);
    return v___x_3643_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3644_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3645_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2,
    );
    v___x_3646_ = lean_string_append(v___x_3645_, v___x_3644_);
    return v___x_3646_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3650_ = 1;
    v___x_3651_ = l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5;
    v___x_3652_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3651_, v___x_3650_);
    return v___x_3652_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3653_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6,
    );
    v___x_3654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3,
    );
    v___x_3655_ = lean_string_append(v___x_3654_, v___x_3653_);
    return v___x_3655_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7,
    );
    v___x_3658_ = lean_string_append(v___x_3657_, v___x_3656_);
    return v___x_3658_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(
    mut v_json_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_a_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3675_: u8 = 0;
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut v_a_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3683_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3660_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0;
                v___x_3661_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_json_3659_, v___x_3660_);
                if crate::leanh::lean_obj_tag(v___x_3661_) == 0 {
                    v_a_3662_ = crate::leanh::lean_ctor_get(v___x_3661_, 0);
                    v_isSharedCheck_3671_ = (!crate::leanh::lean_is_exclusive(v___x_3661_)) as u8;
                    if v_isSharedCheck_3671_ == 0 {
                        v___x_3664_ = v___x_3661_;
                        v_isShared_3665_ = v_isSharedCheck_3671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3662_);
                        crate::leanh::lean_dec(v___x_3661_);
                        v___x_3664_ = crate::leanh::lean_box(0);
                        v_isShared_3665_ = v_isSharedCheck_3671_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3661_) == 0 {
                        v_a_3672_ = crate::leanh::lean_ctor_get(v___x_3661_, 0);
                        v_isSharedCheck_3679_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3661_)) as u8;
                        if v_isSharedCheck_3679_ == 0 {
                            v___x_3674_ = v___x_3661_;
                            v_isShared_3675_ = v_isSharedCheck_3679_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3672_);
                            crate::leanh::lean_dec(v___x_3661_);
                            v___x_3674_ = crate::leanh::lean_box(0);
                            v_isShared_3675_ = v_isSharedCheck_3679_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3680_ = crate::leanh::lean_ctor_get(v___x_3661_, 0);
                        v_isSharedCheck_3687_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3661_)) as u8;
                        if v_isSharedCheck_3687_ == 0 {
                            v___x_3682_ = v___x_3661_;
                            v_isShared_3683_ = v_isSharedCheck_3687_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3680_);
                            crate::leanh::lean_dec(v___x_3661_);
                            v___x_3682_ = crate::leanh::lean_box(0);
                            v_isShared_3683_ = v_isSharedCheck_3687_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3666_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8,
                );
                v___x_3667_ = lean_string_append(v___x_3666_, v_a_3662_);
                crate::leanh::lean_dec(v_a_3662_);
                if v_isShared_3665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3664_, 0, v___x_3667_);
                    v___x_3669_ = v___x_3664_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
                    v___x_3669_ = v_reuseFailAlloc_3670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3669_;
            }
            3 => {
                if v_isShared_3675_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3674_, 0);
                    v___x_3677_ = v___x_3674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
                    v___x_3677_ = v_reuseFailAlloc_3678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3677_;
            }
            5 => {
                if v_isShared_3683_ == 0 {
                    v___x_3685_ = v___x_3682_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
                    v___x_3685_ = v_reuseFailAlloc_3686_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(
    mut v_x_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0;
    v___x_3693_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
            v___x_3692_,
            v_x_3691_,
        );
    v___x_3694_ = crate::leanh::lean_box(0);
    v___x_3695_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3695_, 0, v___x_3693_);
    crate::leanh::lean_ctor_set(v___x_3695_, 1, v___x_3694_);
    v___x_3696_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3697_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3695_, v___x_3696_);
    v___x_3698_ = l_Lean_Json_mkObj(v___x_3697_);
    crate::leanh::lean_dec(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed(
    mut v_x_3699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3700_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_x_3699_);
    crate::leanh::lean_dec(v_x_3699_);
    return v_res_3700_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3708_ = 1;
    v___x_3709_ = l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1;
    v___x_3710_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3709_, v___x_3708_);
    return v___x_3710_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3712_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2,
    );
    v___x_3713_ = lean_string_append(v___x_3712_, v___x_3711_);
    return v___x_3713_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = 1;
    v___x_3718_ = l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5;
    v___x_3719_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3718_, v___x_3717_);
    return v___x_3719_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6,
    );
    v___x_3721_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3,
    );
    v___x_3722_ = lean_string_append(v___x_3721_, v___x_3720_);
    return v___x_3722_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3724_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7,
    );
    v___x_3725_ = lean_string_append(v___x_3724_, v___x_3723_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(
    mut v_json_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3738_: u8 = 0;
    let mut v_a_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3742_: u8 = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut v_a_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3727_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0;
                v___x_3728_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_3726_, v___x_3727_);
                if crate::leanh::lean_obj_tag(v___x_3728_) == 0 {
                    v_a_3729_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
                    v_isSharedCheck_3738_ = (!crate::leanh::lean_is_exclusive(v___x_3728_)) as u8;
                    if v_isSharedCheck_3738_ == 0 {
                        v___x_3731_ = v___x_3728_;
                        v_isShared_3732_ = v_isSharedCheck_3738_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3729_);
                        crate::leanh::lean_dec(v___x_3728_);
                        v___x_3731_ = crate::leanh::lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3738_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3728_) == 0 {
                        v_a_3739_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
                        v_isSharedCheck_3746_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3728_)) as u8;
                        if v_isSharedCheck_3746_ == 0 {
                            v___x_3741_ = v___x_3728_;
                            v_isShared_3742_ = v_isSharedCheck_3746_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3739_);
                            crate::leanh::lean_dec(v___x_3728_);
                            v___x_3741_ = crate::leanh::lean_box(0);
                            v_isShared_3742_ = v_isSharedCheck_3746_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3747_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
                        v_isSharedCheck_3754_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3728_)) as u8;
                        if v_isSharedCheck_3754_ == 0 {
                            v___x_3749_ = v___x_3728_;
                            v_isShared_3750_ = v_isSharedCheck_3754_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3747_);
                            crate::leanh::lean_dec(v___x_3728_);
                            v___x_3749_ = crate::leanh::lean_box(0);
                            v_isShared_3750_ = v_isSharedCheck_3754_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3733_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8,
                );
                v___x_3734_ = lean_string_append(v___x_3733_, v_a_3729_);
                crate::leanh::lean_dec(v_a_3729_);
                if v_isShared_3732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3731_, 0, v___x_3734_);
                    v___x_3736_ = v___x_3731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
                    v___x_3736_ = v_reuseFailAlloc_3737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3736_;
            }
            3 => {
                if v_isShared_3742_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3741_, 0);
                    v___x_3744_ = v___x_3741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
                    v___x_3744_ = v_reuseFailAlloc_3745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3744_;
            }
            5 => {
                if v_isShared_3750_ == 0 {
                    v___x_3752_ = v___x_3749_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
                    v___x_3752_ = v_reuseFailAlloc_3753_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(
    mut v_k_3757_: *mut crate::leanh::LeanObject,
    mut v_x_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3758_) == 0 {
        let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3757_);
        v___x_3759_ = crate::leanh::lean_box(0);
        return v___x_3759_;
    } else {
        let mut v_val_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3760_ = crate::leanh::lean_ctor_get(v_x_3758_, 0);
        v___x_3761_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_val_3760_);
        v___x_3762_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3762_, 0, v_k_3757_);
        crate::leanh::lean_ctor_set(v___x_3762_, 1, v___x_3761_);
        v___x_3763_ = crate::leanh::lean_box(0);
        v___x_3764_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3764_, 0, v___x_3762_);
        crate::leanh::lean_ctor_set(v___x_3764_, 1, v___x_3763_);
        return v___x_3764_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0___boxed(
    mut v_k_3765_: *mut crate::leanh::LeanObject,
    mut v_x_3766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3767_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(
            v_k_3765_, v_x_3766_,
        );
    crate::leanh::lean_dec(v_x_3766_);
    return v_res_3767_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(
    mut v_sz_3768_: usize,
    mut v_i_3769_: usize,
    mut v_bs_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3771_: u8 = 0;
    let mut v_v_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: usize = 0;
    let mut v___x_3777_: usize = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3771_ = lean_usize_dec_lt(v_i_3769_, v_sz_3768_);
                if v___x_3771_ == 0 {
                    return v_bs_3770_;
                } else {
                    v_v_3772_ = lean_array_uget(v_bs_3770_, v_i_3769_);
                    v___x_3773_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3774_ = lean_array_uset(v_bs_3770_, v_i_3769_, v___x_3773_);
                    v___x_3775_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3775_, 0, v_v_3772_);
                    v___x_3776_ = 1usize;
                    v___x_3777_ = lean_usize_add(v_i_3769_, v___x_3776_);
                    v___x_3778_ = lean_array_uset(v_bs_x27_3774_, v_i_3769_, v___x_3775_);
                    v_i_3769_ = v___x_3777_;
                    v_bs_3770_ = v___x_3778_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2___boxed(
    mut v_sz_3780_: *mut crate::leanh::LeanObject,
    mut v_i_3781_: *mut crate::leanh::LeanObject,
    mut v_bs_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3783_: usize = 0;
    let mut v_i_boxed_3784_: usize = 0;
    let mut v_res_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3783_ = crate::leanh::lean_unbox_usize(v_sz_3780_);
    crate::leanh::lean_dec(v_sz_3780_);
    v_i_boxed_3784_ = crate::leanh::lean_unbox_usize(v_i_3781_);
    crate::leanh::lean_dec(v_i_3781_);
    v_res_3785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_boxed_3783_, v_i_boxed_3784_, v_bs_3782_);
    return v_res_3785_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(
    mut v_a_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3787_: usize = 0;
    let mut v___x_3788_: usize = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_3787_ = lean_array_size(v_a_3786_);
    v___x_3788_ = 0usize;
    v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_3787_, v___x_3788_, v_a_3786_);
    v___x_3790_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3789_);
    return v___x_3790_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(
    mut v_k_3791_: *mut crate::leanh::LeanObject,
    mut v_x_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3792_) == 0 {
        let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3791_);
        v___x_3793_ = crate::leanh::lean_box(0);
        return v___x_3793_;
    } else {
        let mut v_val_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3794_ = crate::leanh::lean_ctor_get(v_x_3792_, 0);
        crate::leanh::lean_inc(v_val_3794_);
        crate::leanh::lean_dec_ref_known(v_x_3792_, 1);
        v___x_3795_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(v_val_3794_);
        v___x_3796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3796_, 0, v_k_3791_);
        crate::leanh::lean_ctor_set(v___x_3796_, 1, v___x_3795_);
        v___x_3797_ = crate::leanh::lean_box(0);
        v___x_3798_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3798_, 0, v___x_3796_);
        crate::leanh::lean_ctor_set(v___x_3798_, 1, v___x_3797_);
        return v___x_3798_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(
    mut v_x_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_documentChanges_x3f_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changeAnnotationSupport_x3f_3804_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_resourceOperations_x3f_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_documentChanges_x3f_3803_ = crate::leanh::lean_ctor_get(v_x_3802_, 0);
    crate::leanh::lean_inc(v_documentChanges_x3f_3803_);
    v_changeAnnotationSupport_x3f_3804_ = crate::leanh::lean_ctor_get(v_x_3802_, 1);
    crate::leanh::lean_inc(v_changeAnnotationSupport_x3f_3804_);
    v_resourceOperations_x3f_3805_ = crate::leanh::lean_ctor_get(v_x_3802_, 2);
    crate::leanh::lean_inc(v_resourceOperations_x3f_3805_);
    crate::leanh::lean_dec_ref(v_x_3802_);
    v___x_3806_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0;
    v___x_3807_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
            v___x_3806_,
            v_documentChanges_x3f_3803_,
        );
    crate::leanh::lean_dec(v_documentChanges_x3f_3803_);
    v___x_3808_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1;
    v___x_3809_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(
            v___x_3808_,
            v_changeAnnotationSupport_x3f_3804_,
        );
    crate::leanh::lean_dec(v_changeAnnotationSupport_x3f_3804_);
    v___x_3810_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2;
    v___x_3811_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(
            v___x_3810_,
            v_resourceOperations_x3f_3805_,
        );
    v___x_3812_ = crate::leanh::lean_box(0);
    v___x_3813_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3813_, 0, v___x_3811_);
    crate::leanh::lean_ctor_set(v___x_3813_, 1, v___x_3812_);
    v___x_3814_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3814_, 0, v___x_3809_);
    crate::leanh::lean_ctor_set(v___x_3814_, 1, v___x_3813_);
    v___x_3815_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3807_);
    crate::leanh::lean_ctor_set(v___x_3815_, 1, v___x_3814_);
    v___x_3816_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_3817_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_3815_, v___x_3816_);
    v___x_3818_ = l_Lean_Json_mkObj(v___x_3817_);
    crate::leanh::lean_dec(v___x_3817_);
    return v___x_3818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(
    mut v_sz_3821_: usize,
    mut v_i_3822_: usize,
    mut v_bs_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_a_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: usize = 0;
    let mut v___x_3840_: usize = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3824_ = lean_usize_dec_lt(v_i_3822_, v_sz_3821_);
                if v___x_3824_ == 0 {
                    v___x_3825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3825_, 0, v_bs_3823_);
                    return v___x_3825_;
                } else {
                    v_v_3826_ = lean_array_uget_borrowed(v_bs_3823_, v_i_3822_);
                    crate::leanh::lean_inc(v_v_3826_);
                    v___x_3827_ = l_Lean_Json_getStr_x3f(v_v_3826_);
                    if crate::leanh::lean_obj_tag(v___x_3827_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_3823_);
                        v_a_3828_ = crate::leanh::lean_ctor_get(v___x_3827_, 0);
                        v_isSharedCheck_3835_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3827_)) as u8;
                        if v_isSharedCheck_3835_ == 0 {
                            v___x_3830_ = v___x_3827_;
                            v_isShared_3831_ = v_isSharedCheck_3835_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3828_);
                            crate::leanh::lean_dec(v___x_3827_);
                            v___x_3830_ = crate::leanh::lean_box(0);
                            v_isShared_3831_ = v_isSharedCheck_3835_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3836_ = crate::leanh::lean_ctor_get(v___x_3827_, 0);
                        crate::leanh::lean_inc(v_a_3836_);
                        crate::leanh::lean_dec_ref_known(v___x_3827_, 1);
                        v___x_3837_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3838_ = lean_array_uset(v_bs_3823_, v_i_3822_, v___x_3837_);
                        v___x_3839_ = 1usize;
                        v___x_3840_ = lean_usize_add(v_i_3822_, v___x_3839_);
                        v___x_3841_ = lean_array_uset(v_bs_x27_3838_, v_i_3822_, v_a_3836_);
                        v_i_3822_ = v___x_3840_;
                        v_bs_3823_ = v___x_3841_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3831_ == 0 {
                    v___x_3833_ = v___x_3830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
                    v___x_3833_ = v_reuseFailAlloc_3834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_sz_3843_: *mut crate::leanh::LeanObject,
    mut v_i_3844_: *mut crate::leanh::LeanObject,
    mut v_bs_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3846_: usize = 0;
    let mut v_i_boxed_3847_: usize = 0;
    let mut v_res_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3846_ = crate::leanh::lean_unbox_usize(v_sz_3843_);
    crate::leanh::lean_dec(v_sz_3843_);
    v_i_boxed_3847_ = crate::leanh::lean_unbox_usize(v_i_3844_);
    crate::leanh::lean_dec(v_i_3844_);
    v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_boxed_3846_, v_i_boxed_3847_, v_bs_3845_);
    return v_res_3848_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(
    mut v_x_3851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3851_) == 4 {
        let mut v_elems_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3853_: usize = 0;
        let mut v___x_3854_: usize = 0;
        let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_3852_ = crate::leanh::lean_ctor_get(v_x_3851_, 0);
        crate::leanh::lean_inc_ref(v_elems_3852_);
        crate::leanh::lean_dec_ref_known(v_x_3851_, 1);
        v_sz_3853_ = lean_array_size(v_elems_3852_);
        v___x_3854_ = 0usize;
        v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_3853_, v___x_3854_, v_elems_3852_);
        return v___x_3855_;
    } else {
        let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3856_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0;
        v___x_3857_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_3858_ = l_Lean_Json_pretty(v_x_3851_, v___x_3857_);
        v___x_3859_ = lean_string_append(v___x_3856_, v___x_3858_);
        crate::leanh::lean_dec_ref(v___x_3858_);
        v___x_3860_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1;
        v___x_3861_ = lean_string_append(v___x_3859_, v___x_3860_);
        v___x_3862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3862_, 0, v___x_3861_);
        return v___x_3862_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(
    mut v_x_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3871_: u8 = 0;
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut v_a_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3865_) == 0 {
                    v___x_3866_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0;
                    return v___x_3866_;
                } else {
                    v___x_3867_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(v_x_3865_);
                    if crate::leanh::lean_obj_tag(v___x_3867_) == 0 {
                        v_a_3868_ = crate::leanh::lean_ctor_get(v___x_3867_, 0);
                        v_isSharedCheck_3875_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3867_)) as u8;
                        if v_isSharedCheck_3875_ == 0 {
                            v___x_3870_ = v___x_3867_;
                            v_isShared_3871_ = v_isSharedCheck_3875_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3868_);
                            crate::leanh::lean_dec(v___x_3867_);
                            v___x_3870_ = crate::leanh::lean_box(0);
                            v_isShared_3871_ = v_isSharedCheck_3875_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3876_ = crate::leanh::lean_ctor_get(v___x_3867_, 0);
                        v_isSharedCheck_3884_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3867_)) as u8;
                        if v_isSharedCheck_3884_ == 0 {
                            v___x_3878_ = v___x_3867_;
                            v_isShared_3879_ = v_isSharedCheck_3884_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3876_);
                            crate::leanh::lean_dec(v___x_3867_);
                            v___x_3878_ = crate::leanh::lean_box(0);
                            v_isShared_3879_ = v_isSharedCheck_3884_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3871_ == 0 {
                    v___x_3873_ = v___x_3870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
                    v___x_3873_ = v_reuseFailAlloc_3874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3873_;
            }
            3 => {
                v___x_3880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3880_, 0, v_a_3876_);
                if v_isShared_3879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3878_, 0, v___x_3880_);
                    v___x_3882_ = v___x_3878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
                    v___x_3882_ = v_reuseFailAlloc_3883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(
    mut v_j_3885_: *mut crate::leanh::LeanObject,
    mut v_k_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = l_Lean_Json_getObjValD(v_j_3885_, v_k_3886_);
    v___x_3888_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(v___x_3887_);
    return v___x_3888_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1___boxed(
    mut v_j_3889_: *mut crate::leanh::LeanObject,
    mut v_k_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3891_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_j_3889_, v_k_3890_);
    crate::leanh::lean_dec_ref(v_k_3890_);
    return v_res_3891_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_3892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3898_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3892_) == 0 {
                    v___x_3893_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_3893_;
                } else {
                    v___x_3894_ =
                        l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(v_x_3892_);
                    if crate::leanh::lean_obj_tag(v___x_3894_) == 0 {
                        v_a_3895_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
                        v_isSharedCheck_3902_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3894_)) as u8;
                        if v_isSharedCheck_3902_ == 0 {
                            v___x_3897_ = v___x_3894_;
                            v_isShared_3898_ = v_isSharedCheck_3902_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3895_);
                            crate::leanh::lean_dec(v___x_3894_);
                            v___x_3897_ = crate::leanh::lean_box(0);
                            v_isShared_3898_ = v_isSharedCheck_3902_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3903_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
                        v_isSharedCheck_3911_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3894_)) as u8;
                        if v_isSharedCheck_3911_ == 0 {
                            v___x_3905_ = v___x_3894_;
                            v_isShared_3906_ = v_isSharedCheck_3911_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3903_);
                            crate::leanh::lean_dec(v___x_3894_);
                            v___x_3905_ = crate::leanh::lean_box(0);
                            v_isShared_3906_ = v_isSharedCheck_3911_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3898_ == 0 {
                    v___x_3900_ = v___x_3897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
                    v___x_3900_ = v_reuseFailAlloc_3901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3900_;
            }
            3 => {
                v___x_3907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3907_, 0, v_a_3903_);
                if v_isShared_3906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3905_, 0, v___x_3907_);
                    v___x_3909_ = v___x_3905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
                    v___x_3909_ = v_reuseFailAlloc_3910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(
    mut v_j_3912_: *mut crate::leanh::LeanObject,
    mut v_k_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Lean_Json_getObjValD(v_j_3912_, v_k_3913_);
    v___x_3915_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(v___x_3914_);
    return v___x_3915_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_3916_: *mut crate::leanh::LeanObject,
    mut v_k_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3918_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_j_3916_, v_k_3917_);
    crate::leanh::lean_dec_ref(v_k_3917_);
    return v_res_3918_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3924_ = 1;
    v___x_3925_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1;
    v___x_3926_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3925_, v___x_3924_);
    return v___x_3926_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3927_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_3928_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2,
    );
    v___x_3929_ = lean_string_append(v___x_3928_, v___x_3927_);
    return v___x_3929_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3933_ = 1;
    v___x_3934_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5;
    v___x_3935_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3934_, v___x_3933_);
    return v___x_3935_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6,
    );
    v___x_3937_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3,
    );
    v___x_3938_ = lean_string_append(v___x_3937_, v___x_3936_);
    return v___x_3938_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3940_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7,
    );
    v___x_3941_ = lean_string_append(v___x_3940_, v___x_3939_);
    return v___x_3941_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3945_ = 1;
    v___x_3946_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10;
    v___x_3947_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3946_, v___x_3945_);
    return v___x_3947_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11,
    );
    v___x_3949_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3,
    );
    v___x_3950_ = lean_string_append(v___x_3949_, v___x_3948_);
    return v___x_3950_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3952_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12,
    );
    v___x_3953_ = lean_string_append(v___x_3952_, v___x_3951_);
    return v___x_3953_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = 1;
    v___x_3958_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15;
    v___x_3959_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3958_, v___x_3957_);
    return v___x_3959_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16,
    );
    v___x_3961_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3,
    );
    v___x_3962_ = lean_string_append(v___x_3961_, v___x_3960_);
    return v___x_3962_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3963_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_3964_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17,
    );
    v___x_3965_ = lean_string_append(v___x_3964_, v___x_3963_);
    return v___x_3965_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(
    mut v_json_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_a_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3999_: u8 = 0;
    let mut v_a_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4003_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4007_: u8 = 0;
    let mut v_a_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4024_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_a_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3967_ =
                    l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0;
                crate::leanh::lean_inc(v_json_3966_);
                v___x_3968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_3966_, v___x_3967_);
                if crate::leanh::lean_obj_tag(v___x_3968_) == 0 {
                    crate::leanh::lean_dec(v_json_3966_);
                    v_a_3969_ = crate::leanh::lean_ctor_get(v___x_3968_, 0);
                    v_isSharedCheck_3978_ = (!crate::leanh::lean_is_exclusive(v___x_3968_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v___x_3971_ = v___x_3968_;
                        v_isShared_3972_ = v_isSharedCheck_3978_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3969_);
                        crate::leanh::lean_dec(v___x_3968_);
                        v___x_3971_ = crate::leanh::lean_box(0);
                        v_isShared_3972_ = v_isSharedCheck_3978_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3968_) == 0 {
                        crate::leanh::lean_dec(v_json_3966_);
                        v_a_3979_ = crate::leanh::lean_ctor_get(v___x_3968_, 0);
                        v_isSharedCheck_3986_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3968_)) as u8;
                        if v_isSharedCheck_3986_ == 0 {
                            v___x_3981_ = v___x_3968_;
                            v_isShared_3982_ = v_isSharedCheck_3986_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3979_);
                            crate::leanh::lean_dec(v___x_3968_);
                            v___x_3981_ = crate::leanh::lean_box(0);
                            v_isShared_3982_ = v_isSharedCheck_3986_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3987_ = crate::leanh::lean_ctor_get(v___x_3968_, 0);
                        crate::leanh::lean_inc(v_a_3987_);
                        crate::leanh::lean_dec_ref_known(v___x_3968_, 1);
                        v___x_3988_ =
                            l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_3966_);
                        v___x_3989_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_json_3966_, v___x_3988_);
                        if crate::leanh::lean_obj_tag(v___x_3989_) == 0 {
                            crate::leanh::lean_dec(v_a_3987_);
                            crate::leanh::lean_dec(v_json_3966_);
                            v_a_3990_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                            v_isSharedCheck_3999_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3989_)) as u8;
                            if v_isSharedCheck_3999_ == 0 {
                                v___x_3992_ = v___x_3989_;
                                v_isShared_3993_ = v_isSharedCheck_3999_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3990_);
                                crate::leanh::lean_dec(v___x_3989_);
                                v___x_3992_ = crate::leanh::lean_box(0);
                                v_isShared_3993_ = v_isSharedCheck_3999_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3989_) == 0 {
                                crate::leanh::lean_dec(v_a_3987_);
                                crate::leanh::lean_dec(v_json_3966_);
                                v_a_4000_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                                v_isSharedCheck_4007_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3989_)) as u8;
                                if v_isSharedCheck_4007_ == 0 {
                                    v___x_4002_ = v___x_3989_;
                                    v_isShared_4003_ = v_isSharedCheck_4007_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4000_);
                                    crate::leanh::lean_dec(v___x_3989_);
                                    v___x_4002_ = crate::leanh::lean_box(0);
                                    v_isShared_4003_ = v_isSharedCheck_4007_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4008_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                                crate::leanh::lean_inc(v_a_4008_);
                                crate::leanh::lean_dec_ref_known(v___x_3989_, 1);
                                v___x_4009_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2;
                                v___x_4010_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_json_3966_, v___x_4009_);
                                if crate::leanh::lean_obj_tag(v___x_4010_) == 0 {
                                    crate::leanh::lean_dec(v_a_4008_);
                                    crate::leanh::lean_dec(v_a_3987_);
                                    v_a_4011_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                                    v_isSharedCheck_4020_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                                    if v_isSharedCheck_4020_ == 0 {
                                        v___x_4013_ = v___x_4010_;
                                        v_isShared_4014_ = v_isSharedCheck_4020_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4011_);
                                        crate::leanh::lean_dec(v___x_4010_);
                                        v___x_4013_ = crate::leanh::lean_box(0);
                                        v_isShared_4014_ = v_isSharedCheck_4020_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_4010_) == 0 {
                                        crate::leanh::lean_dec(v_a_4008_);
                                        crate::leanh::lean_dec(v_a_3987_);
                                        v_a_4021_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                                        v_isSharedCheck_4028_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                                        if v_isSharedCheck_4028_ == 0 {
                                            v___x_4023_ = v___x_4010_;
                                            v_isShared_4024_ = v_isSharedCheck_4028_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4021_);
                                            crate::leanh::lean_dec(v___x_4010_);
                                            v___x_4023_ = crate::leanh::lean_box(0);
                                            v_isShared_4024_ = v_isSharedCheck_4028_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4029_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                                        v_isSharedCheck_4037_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                                        if v_isSharedCheck_4037_ == 0 {
                                            v___x_4031_ = v___x_4010_;
                                            v_isShared_4032_ = v_isSharedCheck_4037_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4029_);
                                            crate::leanh::lean_dec(v___x_4010_);
                                            v___x_4031_ = crate::leanh::lean_box(0);
                                            v_isShared_4032_ = v_isSharedCheck_4037_;
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
                v___x_3973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8);
                v___x_3974_ = lean_string_append(v___x_3973_, v_a_3969_);
                crate::leanh::lean_dec(v_a_3969_);
                if v_isShared_3972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3971_, 0, v___x_3974_);
                    v___x_3976_ = v___x_3971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3976_;
            }
            3 => {
                if v_isShared_3982_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3981_, 0);
                    v___x_3984_ = v___x_3981_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
                    v___x_3984_ = v_reuseFailAlloc_3985_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3984_;
            }
            5 => {
                v___x_3994_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13_once), _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13);
                v___x_3995_ = lean_string_append(v___x_3994_, v_a_3990_);
                crate::leanh::lean_dec(v_a_3990_);
                if v_isShared_3993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3992_, 0, v___x_3995_);
                    v___x_3997_ = v___x_3992_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3998_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
                    v___x_3997_ = v_reuseFailAlloc_3998_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3997_;
            }
            7 => {
                if v_isShared_4003_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4002_, 0);
                    v___x_4005_ = v___x_4002_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
                    v___x_4005_ = v_reuseFailAlloc_4006_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4005_;
            }
            9 => {
                v___x_4015_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18_once), _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18);
                v___x_4016_ = lean_string_append(v___x_4015_, v_a_4011_);
                crate::leanh::lean_dec(v_a_4011_);
                if v_isShared_4014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4016_);
                    v___x_4018_ = v___x_4013_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4018_;
            }
            11 => {
                if v_isShared_4024_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4023_, 0);
                    v___x_4026_ = v___x_4023_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4026_;
            }
            13 => {
                v___x_4033_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4033_, 0, v_a_3987_);
                crate::leanh::lean_ctor_set(v___x_4033_, 1, v_a_4008_);
                crate::leanh::lean_ctor_set(v___x_4033_, 2, v_a_4029_);
                if v_isShared_4032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4031_, 0, v___x_4033_);
                    v___x_4035_ = v___x_4031_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
                    v___x_4035_ = v_reuseFailAlloc_4036_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(
    mut v_k_4040_: *mut crate::leanh::LeanObject,
    mut v_x_4041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4041_) == 0 {
        let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4040_);
        v___x_4042_ = crate::leanh::lean_box(0);
        return v___x_4042_;
    } else {
        let mut v_val_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4043_ = crate::leanh::lean_ctor_get(v_x_4041_, 0);
        crate::leanh::lean_inc(v_val_4043_);
        crate::leanh::lean_dec_ref_known(v_x_4041_, 1);
        v___x_4044_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(v_val_4043_);
        v___x_4045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4045_, 0, v_k_4040_);
        crate::leanh::lean_ctor_set(v___x_4045_, 1, v___x_4044_);
        v___x_4046_ = crate::leanh::lean_box(0);
        v___x_4047_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4045_);
        crate::leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
        return v___x_4047_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(
    mut v_x_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_applyEdit_x3f_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_workspaceEdit_x3f_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_applyEdit_x3f_4051_ = crate::leanh::lean_ctor_get(v_x_4050_, 0);
                v_workspaceEdit_x3f_4052_ = crate::leanh::lean_ctor_get(v_x_4050_, 1);
                v_isSharedCheck_4068_ = (!crate::leanh::lean_is_exclusive(v_x_4050_)) as u8;
                if v_isSharedCheck_4068_ == 0 {
                    v___x_4054_ = v_x_4050_;
                    v_isShared_4055_ = v_isSharedCheck_4068_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_workspaceEdit_x3f_4052_);
                    crate::leanh::lean_inc(v_applyEdit_x3f_4051_);
                    crate::leanh::lean_dec(v_x_4050_);
                    v___x_4054_ = crate::leanh::lean_box(0);
                    v_isShared_4055_ = v_isSharedCheck_4068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4056_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0;
                v___x_4057_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_4056_, v_applyEdit_x3f_4051_);
                crate::leanh::lean_dec(v_applyEdit_x3f_4051_);
                v___x_4058_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1;
                v___x_4059_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(v___x_4058_, v_workspaceEdit_x3f_4052_);
                v___x_4060_ = crate::leanh::lean_box(0);
                if v_isShared_4055_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4054_, 1);
                    crate::leanh::lean_ctor_set(v___x_4054_, 1, v___x_4060_);
                    crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4059_);
                    v___x_4062_ = v___x_4054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4063_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4057_);
                crate::leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                v___x_4064_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
                v___x_4065_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_4063_, v___x_4064_);
                v___x_4066_ = l_Lean_Json_mkObj(v___x_4065_);
                crate::leanh::lean_dec(v___x_4065_);
                return v___x_4066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v_a_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4087_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4073_) == 0 {
                    v___x_4074_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4074_;
                } else {
                    v___x_4075_ =
                        l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(v_x_4073_);
                    if crate::leanh::lean_obj_tag(v___x_4075_) == 0 {
                        v_a_4076_ = crate::leanh::lean_ctor_get(v___x_4075_, 0);
                        v_isSharedCheck_4083_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4075_)) as u8;
                        if v_isSharedCheck_4083_ == 0 {
                            v___x_4078_ = v___x_4075_;
                            v_isShared_4079_ = v_isSharedCheck_4083_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4076_);
                            crate::leanh::lean_dec(v___x_4075_);
                            v___x_4078_ = crate::leanh::lean_box(0);
                            v_isShared_4079_ = v_isSharedCheck_4083_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4084_ = crate::leanh::lean_ctor_get(v___x_4075_, 0);
                        v_isSharedCheck_4092_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4075_)) as u8;
                        if v_isSharedCheck_4092_ == 0 {
                            v___x_4086_ = v___x_4075_;
                            v_isShared_4087_ = v_isSharedCheck_4092_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4084_);
                            crate::leanh::lean_dec(v___x_4075_);
                            v___x_4086_ = crate::leanh::lean_box(0);
                            v_isShared_4087_ = v_isSharedCheck_4092_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4079_ == 0 {
                    v___x_4081_ = v___x_4078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
                    v___x_4081_ = v_reuseFailAlloc_4082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4081_;
            }
            3 => {
                v___x_4088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4088_, 0, v_a_4084_);
                if v_isShared_4087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4088_);
                    v___x_4090_ = v___x_4086_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
                    v___x_4090_ = v_reuseFailAlloc_4091_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(
    mut v_j_4093_: *mut crate::leanh::LeanObject,
    mut v_k_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_Json_getObjValD(v_j_4093_, v_k_4094_);
    v___x_4096_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(v___x_4095_);
    return v___x_4096_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_4097_: *mut crate::leanh::LeanObject,
    mut v_k_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4099_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_j_4097_, v_k_4098_);
    crate::leanh::lean_dec_ref(v_k_4098_);
    return v_res_4099_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = 1;
    v___x_4106_ = l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1;
    v___x_4107_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4106_, v___x_4105_);
    return v___x_4107_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4108_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_4109_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2,
    );
    v___x_4110_ = lean_string_append(v___x_4109_, v___x_4108_);
    return v___x_4110_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = 1;
    v___x_4115_ = l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5;
    v___x_4116_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4115_, v___x_4114_);
    return v___x_4116_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6,
    );
    v___x_4118_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3,
    );
    v___x_4119_ = lean_string_append(v___x_4118_, v___x_4117_);
    return v___x_4119_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4120_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4121_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7,
    );
    v___x_4122_ = lean_string_append(v___x_4121_, v___x_4120_);
    return v___x_4122_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4126_ = 1;
    v___x_4127_ = l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10;
    v___x_4128_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4127_, v___x_4126_);
    return v___x_4128_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11,
    );
    v___x_4130_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3,
    );
    v___x_4131_ = lean_string_append(v___x_4130_, v___x_4129_);
    return v___x_4131_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4132_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12,
    );
    v___x_4134_ = lean_string_append(v___x_4133_, v___x_4132_);
    return v___x_4134_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(
    mut v_json_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_a_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut v_a_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4136_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0;
                crate::leanh::lean_inc(v_json_4135_);
                v___x_4137_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_4135_, v___x_4136_);
                if crate::leanh::lean_obj_tag(v___x_4137_) == 0 {
                    crate::leanh::lean_dec(v_json_4135_);
                    v_a_4138_ = crate::leanh::lean_ctor_get(v___x_4137_, 0);
                    v_isSharedCheck_4147_ = (!crate::leanh::lean_is_exclusive(v___x_4137_)) as u8;
                    if v_isSharedCheck_4147_ == 0 {
                        v___x_4140_ = v___x_4137_;
                        v_isShared_4141_ = v_isSharedCheck_4147_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4138_);
                        crate::leanh::lean_dec(v___x_4137_);
                        v___x_4140_ = crate::leanh::lean_box(0);
                        v_isShared_4141_ = v_isSharedCheck_4147_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4137_) == 0 {
                        crate::leanh::lean_dec(v_json_4135_);
                        v_a_4148_ = crate::leanh::lean_ctor_get(v___x_4137_, 0);
                        v_isSharedCheck_4155_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4137_)) as u8;
                        if v_isSharedCheck_4155_ == 0 {
                            v___x_4150_ = v___x_4137_;
                            v_isShared_4151_ = v_isSharedCheck_4155_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4148_);
                            crate::leanh::lean_dec(v___x_4137_);
                            v___x_4150_ = crate::leanh::lean_box(0);
                            v_isShared_4151_ = v_isSharedCheck_4155_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4156_ = crate::leanh::lean_ctor_get(v___x_4137_, 0);
                        crate::leanh::lean_inc(v_a_4156_);
                        crate::leanh::lean_dec_ref_known(v___x_4137_, 1);
                        v___x_4157_ =
                            l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1;
                        v___x_4158_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_json_4135_, v___x_4157_);
                        if crate::leanh::lean_obj_tag(v___x_4158_) == 0 {
                            crate::leanh::lean_dec(v_a_4156_);
                            v_a_4159_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                            v_isSharedCheck_4168_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                            if v_isSharedCheck_4168_ == 0 {
                                v___x_4161_ = v___x_4158_;
                                v_isShared_4162_ = v_isSharedCheck_4168_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4159_);
                                crate::leanh::lean_dec(v___x_4158_);
                                v___x_4161_ = crate::leanh::lean_box(0);
                                v_isShared_4162_ = v_isSharedCheck_4168_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4158_) == 0 {
                                crate::leanh::lean_dec(v_a_4156_);
                                v_a_4169_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                                v_isSharedCheck_4176_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                                if v_isSharedCheck_4176_ == 0 {
                                    v___x_4171_ = v___x_4158_;
                                    v_isShared_4172_ = v_isSharedCheck_4176_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4169_);
                                    crate::leanh::lean_dec(v___x_4158_);
                                    v___x_4171_ = crate::leanh::lean_box(0);
                                    v_isShared_4172_ = v_isSharedCheck_4176_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4177_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                                v_isSharedCheck_4185_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                                if v_isSharedCheck_4185_ == 0 {
                                    v___x_4179_ = v___x_4158_;
                                    v_isShared_4180_ = v_isSharedCheck_4185_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4177_);
                                    crate::leanh::lean_dec(v___x_4158_);
                                    v___x_4179_ = crate::leanh::lean_box(0);
                                    v_isShared_4180_ = v_isSharedCheck_4185_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4142_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8);
                v___x_4143_ = lean_string_append(v___x_4142_, v_a_4138_);
                crate::leanh::lean_dec(v_a_4138_);
                if v_isShared_4141_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4143_);
                    v___x_4145_ = v___x_4140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4145_;
            }
            3 => {
                if v_isShared_4151_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4150_, 0);
                    v___x_4153_ = v___x_4150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
                    v___x_4153_ = v_reuseFailAlloc_4154_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4153_;
            }
            5 => {
                v___x_4163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13_once), _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13);
                v___x_4164_ = lean_string_append(v___x_4163_, v_a_4159_);
                crate::leanh::lean_dec(v_a_4159_);
                if v_isShared_4162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4161_, 0, v___x_4164_);
                    v___x_4166_ = v___x_4161_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4164_);
                    v___x_4166_ = v_reuseFailAlloc_4167_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4166_;
            }
            7 => {
                if v_isShared_4172_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4171_, 0);
                    v___x_4174_ = v___x_4171_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
                    v___x_4174_ = v_reuseFailAlloc_4175_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4174_;
            }
            9 => {
                v___x_4181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4181_, 0, v_a_4156_);
                crate::leanh::lean_ctor_set(v___x_4181_, 1, v_a_4177_);
                if v_isShared_4180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4179_, 0, v___x_4181_);
                    v___x_4183_ = v___x_4179_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
                    v___x_4183_ = v_reuseFailAlloc_4184_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(
    mut v_k_4188_: *mut crate::leanh::LeanObject,
    mut v_x_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4189_) == 0 {
        let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4188_);
        v___x_4190_ = crate::leanh::lean_box(0);
        return v___x_4190_;
    } else {
        let mut v_val_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4192_: u8 = 0;
        let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4191_ = crate::leanh::lean_ctor_get(v_x_4189_, 0);
        v___x_4192_ = (crate::leanh::lean_unbox(v_val_4191_) as u8);
        v___x_4193_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_4192_);
        v___x_4194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4194_, 0, v_k_4188_);
        crate::leanh::lean_ctor_set(v___x_4194_, 1, v___x_4193_);
        v___x_4195_ = crate::leanh::lean_box(0);
        v___x_4196_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4196_, 0, v___x_4194_);
        crate::leanh::lean_ctor_set(v___x_4196_, 1, v___x_4195_);
        return v___x_4196_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0___boxed(
    mut v_k_4197_: *mut crate::leanh::LeanObject,
    mut v_x_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4199_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(
        v_k_4197_, v_x_4198_,
    );
    crate::leanh::lean_dec(v_x_4198_);
    return v_res_4199_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(
    mut v_x_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_incrementalDiagnosticSupport_x3f_4204_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_silentDiagnosticSupport_x3f_4205_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_rpcWireFormat_x3f_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_incrementalDiagnosticSupport_x3f_4204_ = crate::leanh::lean_ctor_get(v_x_4203_, 0);
    v_silentDiagnosticSupport_x3f_4205_ = crate::leanh::lean_ctor_get(v_x_4203_, 1);
    v_rpcWireFormat_x3f_4206_ = crate::leanh::lean_ctor_get(v_x_4203_, 2);
    v___x_4207_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0;
    v___x_4208_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
            v___x_4207_,
            v_incrementalDiagnosticSupport_x3f_4204_,
        );
    v___x_4209_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1;
    v___x_4210_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(
            v___x_4209_,
            v_silentDiagnosticSupport_x3f_4205_,
        );
    v___x_4211_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2;
    v___x_4212_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(
        v___x_4211_,
        v_rpcWireFormat_x3f_4206_,
    );
    v___x_4213_ = crate::leanh::lean_box(0);
    v___x_4214_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4214_, 0, v___x_4212_);
    crate::leanh::lean_ctor_set(v___x_4214_, 1, v___x_4213_);
    v___x_4215_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4215_, 1, v___x_4214_);
    v___x_4216_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4208_);
    crate::leanh::lean_ctor_set(v___x_4216_, 1, v___x_4215_);
    v___x_4217_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_4218_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_4216_, v___x_4217_);
    v___x_4219_ = l_Lean_Json_mkObj(v___x_4218_);
    crate::leanh::lean_dec(v___x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed(
    mut v_x_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4221_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_x_4220_);
    crate::leanh::lean_dec_ref(v_x_4220_);
    return v_res_4221_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_4226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_a_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4226_) == 0 {
                    v___x_4227_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4227_;
                } else {
                    v___x_4228_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_4226_);
                    if crate::leanh::lean_obj_tag(v___x_4228_) == 0 {
                        v_a_4229_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                        v_isSharedCheck_4236_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                        if v_isSharedCheck_4236_ == 0 {
                            v___x_4231_ = v___x_4228_;
                            v_isShared_4232_ = v_isSharedCheck_4236_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4229_);
                            crate::leanh::lean_dec(v___x_4228_);
                            v___x_4231_ = crate::leanh::lean_box(0);
                            v_isShared_4232_ = v_isSharedCheck_4236_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4237_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                        v_isSharedCheck_4245_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                        if v_isSharedCheck_4245_ == 0 {
                            v___x_4239_ = v___x_4228_;
                            v_isShared_4240_ = v_isSharedCheck_4245_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4237_);
                            crate::leanh::lean_dec(v___x_4228_);
                            v___x_4239_ = crate::leanh::lean_box(0);
                            v_isShared_4240_ = v_isSharedCheck_4245_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4232_ == 0 {
                    v___x_4234_ = v___x_4231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
                    v___x_4234_ = v_reuseFailAlloc_4235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4234_;
            }
            3 => {
                v___x_4241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4241_, 0, v_a_4237_);
                if v_isShared_4240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4239_, 0, v___x_4241_);
                    v___x_4243_ = v___x_4239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
                    v___x_4243_ = v_reuseFailAlloc_4244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(
    mut v_j_4246_: *mut crate::leanh::LeanObject,
    mut v_k_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4248_ = l_Lean_Json_getObjValD(v_j_4246_, v_k_4247_);
    v___x_4249_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(v___x_4248_);
    return v___x_4249_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_4250_: *mut crate::leanh::LeanObject,
    mut v_k_4251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_j_4250_, v_k_4251_);
    crate::leanh::lean_dec_ref(v_k_4251_);
    return v_res_4252_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4258_ = 1;
    v___x_4259_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1;
    v___x_4260_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4259_, v___x_4258_);
    return v___x_4260_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4261_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_4262_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2,
    );
    v___x_4263_ = lean_string_append(v___x_4262_, v___x_4261_);
    return v___x_4263_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ = 1;
    v___x_4268_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5;
    v___x_4269_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4268_, v___x_4267_);
    return v___x_4269_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6,
    );
    v___x_4271_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3,
    );
    v___x_4272_ = lean_string_append(v___x_4271_, v___x_4270_);
    return v___x_4272_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4273_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7,
    );
    v___x_4275_ = lean_string_append(v___x_4274_, v___x_4273_);
    return v___x_4275_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4279_: u8 = 0;
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4279_ = 1;
    v___x_4280_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10;
    v___x_4281_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4280_, v___x_4279_);
    return v___x_4281_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11,
    );
    v___x_4283_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3,
    );
    v___x_4284_ = lean_string_append(v___x_4283_, v___x_4282_);
    return v___x_4284_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12,
    );
    v___x_4287_ = lean_string_append(v___x_4286_, v___x_4285_);
    return v___x_4287_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4291_: u8 = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = 1;
    v___x_4292_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15;
    v___x_4293_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4292_, v___x_4291_);
    return v___x_4293_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16,
    );
    v___x_4295_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3,
    );
    v___x_4296_ = lean_string_append(v___x_4295_, v___x_4294_);
    return v___x_4296_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4298_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17,
    );
    v___x_4299_ = lean_string_append(v___x_4298_, v___x_4297_);
    return v___x_4299_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(
    mut v_json_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4333_: u8 = 0;
    let mut v_a_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_a_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4348_: u8 = 0;
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut v_a_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut v_a_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4301_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0;
                crate::leanh::lean_inc(v_json_4300_);
                v___x_4302_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_4300_, v___x_4301_);
                if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                    crate::leanh::lean_dec(v_json_4300_);
                    v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                    v_isSharedCheck_4312_ = (!crate::leanh::lean_is_exclusive(v___x_4302_)) as u8;
                    if v_isSharedCheck_4312_ == 0 {
                        v___x_4305_ = v___x_4302_;
                        v_isShared_4306_ = v_isSharedCheck_4312_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4303_);
                        crate::leanh::lean_dec(v___x_4302_);
                        v___x_4305_ = crate::leanh::lean_box(0);
                        v_isShared_4306_ = v_isSharedCheck_4312_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                        crate::leanh::lean_dec(v_json_4300_);
                        v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                        v_isSharedCheck_4320_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4302_)) as u8;
                        if v_isSharedCheck_4320_ == 0 {
                            v___x_4315_ = v___x_4302_;
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4313_);
                            crate::leanh::lean_dec(v___x_4302_);
                            v___x_4315_ = crate::leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                        crate::leanh::lean_inc(v_a_4321_);
                        crate::leanh::lean_dec_ref_known(v___x_4302_, 1);
                        v___x_4322_ =
                            l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_4300_);
                        v___x_4323_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_4300_, v___x_4322_);
                        if crate::leanh::lean_obj_tag(v___x_4323_) == 0 {
                            crate::leanh::lean_dec(v_a_4321_);
                            crate::leanh::lean_dec(v_json_4300_);
                            v_a_4324_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                            v_isSharedCheck_4333_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4323_)) as u8;
                            if v_isSharedCheck_4333_ == 0 {
                                v___x_4326_ = v___x_4323_;
                                v_isShared_4327_ = v_isSharedCheck_4333_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4324_);
                                crate::leanh::lean_dec(v___x_4323_);
                                v___x_4326_ = crate::leanh::lean_box(0);
                                v_isShared_4327_ = v_isSharedCheck_4333_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4323_) == 0 {
                                crate::leanh::lean_dec(v_a_4321_);
                                crate::leanh::lean_dec(v_json_4300_);
                                v_a_4334_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                                v_isSharedCheck_4341_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4323_)) as u8;
                                if v_isSharedCheck_4341_ == 0 {
                                    v___x_4336_ = v___x_4323_;
                                    v_isShared_4337_ = v_isSharedCheck_4341_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4334_);
                                    crate::leanh::lean_dec(v___x_4323_);
                                    v___x_4336_ = crate::leanh::lean_box(0);
                                    v_isShared_4337_ = v_isSharedCheck_4341_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4342_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                                crate::leanh::lean_inc(v_a_4342_);
                                crate::leanh::lean_dec_ref_known(v___x_4323_, 1);
                                v___x_4343_ =
                                    l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2;
                                v___x_4344_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_json_4300_, v___x_4343_);
                                if crate::leanh::lean_obj_tag(v___x_4344_) == 0 {
                                    crate::leanh::lean_dec(v_a_4342_);
                                    crate::leanh::lean_dec(v_a_4321_);
                                    v_a_4345_ = crate::leanh::lean_ctor_get(v___x_4344_, 0);
                                    v_isSharedCheck_4354_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4344_)) as u8;
                                    if v_isSharedCheck_4354_ == 0 {
                                        v___x_4347_ = v___x_4344_;
                                        v_isShared_4348_ = v_isSharedCheck_4354_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4345_);
                                        crate::leanh::lean_dec(v___x_4344_);
                                        v___x_4347_ = crate::leanh::lean_box(0);
                                        v_isShared_4348_ = v_isSharedCheck_4354_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_4344_) == 0 {
                                        crate::leanh::lean_dec(v_a_4342_);
                                        crate::leanh::lean_dec(v_a_4321_);
                                        v_a_4355_ = crate::leanh::lean_ctor_get(v___x_4344_, 0);
                                        v_isSharedCheck_4362_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4344_)) as u8;
                                        if v_isSharedCheck_4362_ == 0 {
                                            v___x_4357_ = v___x_4344_;
                                            v_isShared_4358_ = v_isSharedCheck_4362_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4355_);
                                            crate::leanh::lean_dec(v___x_4344_);
                                            v___x_4357_ = crate::leanh::lean_box(0);
                                            v_isShared_4358_ = v_isSharedCheck_4362_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4363_ = crate::leanh::lean_ctor_get(v___x_4344_, 0);
                                        v_isSharedCheck_4371_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4344_)) as u8;
                                        if v_isSharedCheck_4371_ == 0 {
                                            v___x_4365_ = v___x_4344_;
                                            v_isShared_4366_ = v_isSharedCheck_4371_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4363_);
                                            crate::leanh::lean_dec(v___x_4344_);
                                            v___x_4365_ = crate::leanh::lean_box(0);
                                            v_isShared_4366_ = v_isSharedCheck_4371_;
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
                v___x_4307_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8,
                );
                v___x_4308_ = lean_string_append(v___x_4307_, v_a_4303_);
                crate::leanh::lean_dec(v_a_4303_);
                if v_isShared_4306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4305_, 0, v___x_4308_);
                    v___x_4310_ = v___x_4305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
                    v___x_4310_ = v_reuseFailAlloc_4311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4310_;
            }
            3 => {
                if v_isShared_4316_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4315_, 0);
                    v___x_4318_ = v___x_4315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4318_;
            }
            5 => {
                v___x_4328_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13,
                );
                v___x_4329_ = lean_string_append(v___x_4328_, v_a_4324_);
                crate::leanh::lean_dec(v_a_4324_);
                if v_isShared_4327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4326_, 0, v___x_4329_);
                    v___x_4331_ = v___x_4326_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
                    v___x_4331_ = v_reuseFailAlloc_4332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4331_;
            }
            7 => {
                if v_isShared_4337_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4336_, 0);
                    v___x_4339_ = v___x_4336_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
                    v___x_4339_ = v_reuseFailAlloc_4340_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4339_;
            }
            9 => {
                v___x_4349_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18,
                );
                v___x_4350_ = lean_string_append(v___x_4349_, v_a_4345_);
                crate::leanh::lean_dec(v_a_4345_);
                if v_isShared_4348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4347_, 0, v___x_4350_);
                    v___x_4352_ = v___x_4347_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4352_;
            }
            11 => {
                if v_isShared_4358_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4357_, 0);
                    v___x_4360_ = v___x_4357_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
                    v___x_4360_ = v_reuseFailAlloc_4361_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4360_;
            }
            13 => {
                v___x_4367_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4367_, 0, v_a_4321_);
                crate::leanh::lean_ctor_set(v___x_4367_, 1, v_a_4342_);
                crate::leanh::lean_ctor_set(v___x_4367_, 2, v_a_4363_);
                if v_isShared_4366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4365_, 0, v___x_4367_);
                    v___x_4369_ = v___x_4365_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(
    mut v_k_4374_: *mut crate::leanh::LeanObject,
    mut v_x_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4375_) == 0 {
        let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4374_);
        v___x_4376_ = crate::leanh::lean_box(0);
        return v___x_4376_;
    } else {
        let mut v_val_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4377_ = crate::leanh::lean_ctor_get(v_x_4375_, 0);
        crate::leanh::lean_inc(v_val_4377_);
        crate::leanh::lean_dec_ref_known(v_x_4375_, 1);
        v___x_4378_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(v_val_4377_);
        v___x_4379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4379_, 0, v_k_4374_);
        crate::leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
        v___x_4380_ = crate::leanh::lean_box(0);
        v___x_4381_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4379_);
        crate::leanh::lean_ctor_set(v___x_4381_, 1, v___x_4380_);
        return v___x_4381_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(
    mut v_k_4382_: *mut crate::leanh::LeanObject,
    mut v_x_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4383_) == 0 {
        let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4382_);
        v___x_4384_ = crate::leanh::lean_box(0);
        return v___x_4384_;
    } else {
        let mut v_val_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4385_ = crate::leanh::lean_ctor_get(v_x_4383_, 0);
        v___x_4386_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_val_4385_);
        v___x_4387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4387_, 0, v_k_4382_);
        crate::leanh::lean_ctor_set(v___x_4387_, 1, v___x_4386_);
        v___x_4388_ = crate::leanh::lean_box(0);
        v___x_4389_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4389_, 0, v___x_4387_);
        crate::leanh::lean_ctor_set(v___x_4389_, 1, v___x_4388_);
        return v___x_4389_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1___boxed(
    mut v_k_4390_: *mut crate::leanh::LeanObject,
    mut v_x_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(
        v_k_4390_, v_x_4391_,
    );
    crate::leanh::lean_dec(v_x_4391_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(
    mut v_k_4393_: *mut crate::leanh::LeanObject,
    mut v_x_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4394_) == 0 {
        let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4393_);
        v___x_4395_ = crate::leanh::lean_box(0);
        return v___x_4395_;
    } else {
        let mut v_val_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4396_ = crate::leanh::lean_ctor_get(v_x_4394_, 0);
        crate::leanh::lean_inc(v_val_4396_);
        crate::leanh::lean_dec_ref_known(v_x_4394_, 1);
        v___x_4397_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(v_val_4396_);
        v___x_4398_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4398_, 0, v_k_4393_);
        crate::leanh::lean_ctor_set(v___x_4398_, 1, v___x_4397_);
        v___x_4399_ = crate::leanh::lean_box(0);
        v___x_4400_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4400_, 0, v___x_4398_);
        crate::leanh::lean_ctor_set(v___x_4400_, 1, v___x_4399_);
        return v___x_4400_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(
    mut v_k_4401_: *mut crate::leanh::LeanObject,
    mut v_x_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4402_) == 0 {
        let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4401_);
        v___x_4403_ = crate::leanh::lean_box(0);
        return v___x_4403_;
    } else {
        let mut v_val_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4404_ = crate::leanh::lean_ctor_get(v_x_4402_, 0);
        v___x_4405_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_val_4404_);
        v___x_4406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4406_, 0, v_k_4401_);
        crate::leanh::lean_ctor_set(v___x_4406_, 1, v___x_4405_);
        v___x_4407_ = crate::leanh::lean_box(0);
        v___x_4408_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4406_);
        crate::leanh::lean_ctor_set(v___x_4408_, 1, v___x_4407_);
        return v___x_4408_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3___boxed(
    mut v_k_4409_: *mut crate::leanh::LeanObject,
    mut v_x_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(
        v_k_4409_, v_x_4410_,
    );
    crate::leanh::lean_dec(v_x_4410_);
    return v_res_4411_;
}
pub unsafe fn l_Lean_Lsp_instToJsonClientCapabilities_toJson(
    mut v_x_4416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_x3f_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_window_x3f_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_workspace_x3f_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_x3f_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_x3f_4417_ = crate::leanh::lean_ctor_get(v_x_4416_, 0);
    crate::leanh::lean_inc(v_textDocument_x3f_4417_);
    v_window_x3f_4418_ = crate::leanh::lean_ctor_get(v_x_4416_, 1);
    crate::leanh::lean_inc(v_window_x3f_4418_);
    v_workspace_x3f_4419_ = crate::leanh::lean_ctor_get(v_x_4416_, 2);
    crate::leanh::lean_inc(v_workspace_x3f_4419_);
    v_lean_x3f_4420_ = crate::leanh::lean_ctor_get(v_x_4416_, 3);
    crate::leanh::lean_inc(v_lean_x3f_4420_);
    crate::leanh::lean_dec_ref(v_x_4416_);
    v___x_4421_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0;
    v___x_4422_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(
        v___x_4421_,
        v_textDocument_x3f_4417_,
    );
    v___x_4423_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1;
    v___x_4424_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(
        v___x_4423_,
        v_window_x3f_4418_,
    );
    crate::leanh::lean_dec(v_window_x3f_4418_);
    v___x_4425_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2;
    v___x_4426_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(
        v___x_4425_,
        v_workspace_x3f_4419_,
    );
    v___x_4427_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3;
    v___x_4428_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(
        v___x_4427_,
        v_lean_x3f_4420_,
    );
    crate::leanh::lean_dec(v_lean_x3f_4420_);
    v___x_4429_ = crate::leanh::lean_box(0);
    v___x_4430_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4430_, 0, v___x_4428_);
    crate::leanh::lean_ctor_set(v___x_4430_, 1, v___x_4429_);
    v___x_4431_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4431_, 0, v___x_4426_);
    crate::leanh::lean_ctor_set(v___x_4431_, 1, v___x_4430_);
    v___x_4432_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4432_, 0, v___x_4424_);
    crate::leanh::lean_ctor_set(v___x_4432_, 1, v___x_4431_);
    v___x_4433_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4433_, 0, v___x_4422_);
    crate::leanh::lean_ctor_set(v___x_4433_, 1, v___x_4432_);
    v___x_4434_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_4435_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_4433_, v___x_4434_);
    v___x_4436_ = l_Lean_Json_mkObj(v___x_4435_);
    crate::leanh::lean_dec(v___x_4435_);
    return v___x_4436_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(
    mut v_x_4441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4447_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4451_: u8 = 0;
    let mut v_a_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4455_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4441_) == 0 {
                    v___x_4442_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0;
                    return v___x_4442_;
                } else {
                    v___x_4443_ =
                        l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(v_x_4441_);
                    if crate::leanh::lean_obj_tag(v___x_4443_) == 0 {
                        v_a_4444_ = crate::leanh::lean_ctor_get(v___x_4443_, 0);
                        v_isSharedCheck_4451_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4443_)) as u8;
                        if v_isSharedCheck_4451_ == 0 {
                            v___x_4446_ = v___x_4443_;
                            v_isShared_4447_ = v_isSharedCheck_4451_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4444_);
                            crate::leanh::lean_dec(v___x_4443_);
                            v___x_4446_ = crate::leanh::lean_box(0);
                            v_isShared_4447_ = v_isSharedCheck_4451_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4452_ = crate::leanh::lean_ctor_get(v___x_4443_, 0);
                        v_isSharedCheck_4460_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4443_)) as u8;
                        if v_isSharedCheck_4460_ == 0 {
                            v___x_4454_ = v___x_4443_;
                            v_isShared_4455_ = v_isSharedCheck_4460_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4452_);
                            crate::leanh::lean_dec(v___x_4443_);
                            v___x_4454_ = crate::leanh::lean_box(0);
                            v_isShared_4455_ = v_isSharedCheck_4460_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4447_ == 0 {
                    v___x_4449_ = v___x_4446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
                    v___x_4449_ = v_reuseFailAlloc_4450_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4449_;
            }
            3 => {
                v___x_4456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4456_, 0, v_a_4452_);
                if v_isShared_4455_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4454_, 0, v___x_4456_);
                    v___x_4458_ = v___x_4454_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
                    v___x_4458_ = v_reuseFailAlloc_4459_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(
    mut v_j_4461_: *mut crate::leanh::LeanObject,
    mut v_k_4462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_Json_getObjValD(v_j_4461_, v_k_4462_);
    v___x_4464_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(v___x_4463_);
    return v___x_4464_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2___boxed(
    mut v_j_4465_: *mut crate::leanh::LeanObject,
    mut v_k_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4467_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_j_4465_, v_k_4466_);
    crate::leanh::lean_dec_ref(v_k_4466_);
    return v_res_4467_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(
    mut v_x_4470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut v_a_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4470_) == 0 {
                    v___x_4471_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0;
                    return v___x_4471_;
                } else {
                    v___x_4472_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(v_x_4470_);
                    if crate::leanh::lean_obj_tag(v___x_4472_) == 0 {
                        v_a_4473_ = crate::leanh::lean_ctor_get(v___x_4472_, 0);
                        v_isSharedCheck_4480_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4472_)) as u8;
                        if v_isSharedCheck_4480_ == 0 {
                            v___x_4475_ = v___x_4472_;
                            v_isShared_4476_ = v_isSharedCheck_4480_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4473_);
                            crate::leanh::lean_dec(v___x_4472_);
                            v___x_4475_ = crate::leanh::lean_box(0);
                            v_isShared_4476_ = v_isSharedCheck_4480_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4481_ = crate::leanh::lean_ctor_get(v___x_4472_, 0);
                        v_isSharedCheck_4489_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4472_)) as u8;
                        if v_isSharedCheck_4489_ == 0 {
                            v___x_4483_ = v___x_4472_;
                            v_isShared_4484_ = v_isSharedCheck_4489_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4481_);
                            crate::leanh::lean_dec(v___x_4472_);
                            v___x_4483_ = crate::leanh::lean_box(0);
                            v_isShared_4484_ = v_isSharedCheck_4489_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4476_ == 0 {
                    v___x_4478_ = v___x_4475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
                    v___x_4478_ = v_reuseFailAlloc_4479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4478_;
            }
            3 => {
                v___x_4485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4485_, 0, v_a_4481_);
                if v_isShared_4484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4483_, 0, v___x_4485_);
                    v___x_4487_ = v___x_4483_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
                    v___x_4487_ = v_reuseFailAlloc_4488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(
    mut v_j_4490_: *mut crate::leanh::LeanObject,
    mut v_k_4491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4492_ = l_Lean_Json_getObjValD(v_j_4490_, v_k_4491_);
    v___x_4493_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(v___x_4492_);
    return v___x_4493_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3___boxed(
    mut v_j_4494_: *mut crate::leanh::LeanObject,
    mut v_k_4495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_j_4494_, v_k_4495_);
    crate::leanh::lean_dec_ref(v_k_4495_);
    return v_res_4496_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(
    mut v_x_4497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4503_: u8 = 0;
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4507_: u8 = 0;
    let mut v_a_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4511_: u8 = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4497_) == 0 {
                    v___x_4498_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4498_;
                } else {
                    v___x_4499_ =
                        l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(v_x_4497_);
                    if crate::leanh::lean_obj_tag(v___x_4499_) == 0 {
                        v_a_4500_ = crate::leanh::lean_ctor_get(v___x_4499_, 0);
                        v_isSharedCheck_4507_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4499_)) as u8;
                        if v_isSharedCheck_4507_ == 0 {
                            v___x_4502_ = v___x_4499_;
                            v_isShared_4503_ = v_isSharedCheck_4507_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4500_);
                            crate::leanh::lean_dec(v___x_4499_);
                            v___x_4502_ = crate::leanh::lean_box(0);
                            v_isShared_4503_ = v_isSharedCheck_4507_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4508_ = crate::leanh::lean_ctor_get(v___x_4499_, 0);
                        v_isSharedCheck_4516_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4499_)) as u8;
                        if v_isSharedCheck_4516_ == 0 {
                            v___x_4510_ = v___x_4499_;
                            v_isShared_4511_ = v_isSharedCheck_4516_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4508_);
                            crate::leanh::lean_dec(v___x_4499_);
                            v___x_4510_ = crate::leanh::lean_box(0);
                            v_isShared_4511_ = v_isSharedCheck_4516_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4503_ == 0 {
                    v___x_4505_ = v___x_4502_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
                    v___x_4505_ = v_reuseFailAlloc_4506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4505_;
            }
            3 => {
                v___x_4512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4512_, 0, v_a_4508_);
                if v_isShared_4511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4510_, 0, v___x_4512_);
                    v___x_4514_ = v___x_4510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
                    v___x_4514_ = v_reuseFailAlloc_4515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(
    mut v_j_4517_: *mut crate::leanh::LeanObject,
    mut v_k_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Lean_Json_getObjValD(v_j_4517_, v_k_4518_);
    v___x_4520_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(v___x_4519_);
    return v___x_4520_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1___boxed(
    mut v_j_4521_: *mut crate::leanh::LeanObject,
    mut v_k_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_j_4521_, v_k_4522_);
    crate::leanh::lean_dec_ref(v_k_4522_);
    return v_res_4523_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(
    mut v_x_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4532_: u8 = 0;
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4536_: u8 = 0;
    let mut v_a_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4540_: u8 = 0;
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4526_) == 0 {
                    v___x_4527_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4527_;
                } else {
                    v___x_4528_ =
                        l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(v_x_4526_);
                    if crate::leanh::lean_obj_tag(v___x_4528_) == 0 {
                        v_a_4529_ = crate::leanh::lean_ctor_get(v___x_4528_, 0);
                        v_isSharedCheck_4536_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4528_)) as u8;
                        if v_isSharedCheck_4536_ == 0 {
                            v___x_4531_ = v___x_4528_;
                            v_isShared_4532_ = v_isSharedCheck_4536_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4529_);
                            crate::leanh::lean_dec(v___x_4528_);
                            v___x_4531_ = crate::leanh::lean_box(0);
                            v_isShared_4532_ = v_isSharedCheck_4536_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4537_ = crate::leanh::lean_ctor_get(v___x_4528_, 0);
                        v_isSharedCheck_4545_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4528_)) as u8;
                        if v_isSharedCheck_4545_ == 0 {
                            v___x_4539_ = v___x_4528_;
                            v_isShared_4540_ = v_isSharedCheck_4545_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4537_);
                            crate::leanh::lean_dec(v___x_4528_);
                            v___x_4539_ = crate::leanh::lean_box(0);
                            v_isShared_4540_ = v_isSharedCheck_4545_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4532_ == 0 {
                    v___x_4534_ = v___x_4531_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
                    v___x_4534_ = v_reuseFailAlloc_4535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4534_;
            }
            3 => {
                v___x_4541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4541_, 0, v_a_4537_);
                if v_isShared_4540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4539_, 0, v___x_4541_);
                    v___x_4543_ = v___x_4539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4541_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(
    mut v_j_4546_: *mut crate::leanh::LeanObject,
    mut v_k_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4548_ = l_Lean_Json_getObjValD(v_j_4546_, v_k_4547_);
    v___x_4549_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(v___x_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0___boxed(
    mut v_j_4550_: *mut crate::leanh::LeanObject,
    mut v_k_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_j_4550_, v_k_4551_);
    crate::leanh::lean_dec_ref(v_k_4551_);
    return v_res_4552_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = 1;
    v___x_4559_ = l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1;
    v___x_4560_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4559_, v___x_4558_);
    return v___x_4560_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4561_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_4562_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2,
    );
    v___x_4563_ = lean_string_append(v___x_4562_, v___x_4561_);
    return v___x_4563_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4567_ = 1;
    v___x_4568_ = l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5;
    v___x_4569_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4568_, v___x_4567_);
    return v___x_4569_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6,
    );
    v___x_4571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3,
    );
    v___x_4572_ = lean_string_append(v___x_4571_, v___x_4570_);
    return v___x_4572_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4573_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4574_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7,
    );
    v___x_4575_ = lean_string_append(v___x_4574_, v___x_4573_);
    return v___x_4575_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4579_ = 1;
    v___x_4580_ = l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10;
    v___x_4581_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4580_, v___x_4579_);
    return v___x_4581_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11,
    );
    v___x_4583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3,
    );
    v___x_4584_ = lean_string_append(v___x_4583_, v___x_4582_);
    return v___x_4584_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4585_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12,
    );
    v___x_4587_ = lean_string_append(v___x_4586_, v___x_4585_);
    return v___x_4587_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4591_ = 1;
    v___x_4592_ = l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15;
    v___x_4593_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4592_, v___x_4591_);
    return v___x_4593_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4594_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16,
    );
    v___x_4595_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3,
    );
    v___x_4596_ = lean_string_append(v___x_4595_, v___x_4594_);
    return v___x_4596_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4597_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4598_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17,
    );
    v___x_4599_ = lean_string_append(v___x_4598_, v___x_4597_);
    return v___x_4599_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = 1;
    v___x_4604_ = l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20;
    v___x_4605_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4604_, v___x_4603_);
    return v___x_4605_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4606_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21,
    );
    v___x_4607_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3,
    );
    v___x_4608_ = lean_string_append(v___x_4607_, v___x_4606_);
    return v___x_4608_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4610_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22_once
        ),
        _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22,
    );
    v___x_4611_ = lean_string_append(v___x_4610_, v___x_4609_);
    return v___x_4611_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(
    mut v_json_4612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4618_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4624_: u8 = 0;
    let mut v_a_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4628_: u8 = 0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_a_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4639_: u8 = 0;
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v_a_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut v_a_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4660_: u8 = 0;
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4666_: u8 = 0;
    let mut v_a_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_a_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4687_: u8 = 0;
    let mut v_a_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4695_: u8 = 0;
    let mut v_a_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4699_: u8 = 0;
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4613_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0;
                crate::leanh::lean_inc(v_json_4612_);
                v___x_4614_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_json_4612_, v___x_4613_);
                if crate::leanh::lean_obj_tag(v___x_4614_) == 0 {
                    crate::leanh::lean_dec(v_json_4612_);
                    v_a_4615_ = crate::leanh::lean_ctor_get(v___x_4614_, 0);
                    v_isSharedCheck_4624_ = (!crate::leanh::lean_is_exclusive(v___x_4614_)) as u8;
                    if v_isSharedCheck_4624_ == 0 {
                        v___x_4617_ = v___x_4614_;
                        v_isShared_4618_ = v_isSharedCheck_4624_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4615_);
                        crate::leanh::lean_dec(v___x_4614_);
                        v___x_4617_ = crate::leanh::lean_box(0);
                        v_isShared_4618_ = v_isSharedCheck_4624_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4614_) == 0 {
                        crate::leanh::lean_dec(v_json_4612_);
                        v_a_4625_ = crate::leanh::lean_ctor_get(v___x_4614_, 0);
                        v_isSharedCheck_4632_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4614_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4627_ = v___x_4614_;
                            v_isShared_4628_ = v_isSharedCheck_4632_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4625_);
                            crate::leanh::lean_dec(v___x_4614_);
                            v___x_4627_ = crate::leanh::lean_box(0);
                            v_isShared_4628_ = v_isSharedCheck_4632_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4633_ = crate::leanh::lean_ctor_get(v___x_4614_, 0);
                        crate::leanh::lean_inc(v_a_4633_);
                        crate::leanh::lean_dec_ref_known(v___x_4614_, 1);
                        v___x_4634_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_4612_);
                        v___x_4635_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_json_4612_, v___x_4634_);
                        if crate::leanh::lean_obj_tag(v___x_4635_) == 0 {
                            crate::leanh::lean_dec(v_a_4633_);
                            crate::leanh::lean_dec(v_json_4612_);
                            v_a_4636_ = crate::leanh::lean_ctor_get(v___x_4635_, 0);
                            v_isSharedCheck_4645_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4635_)) as u8;
                            if v_isSharedCheck_4645_ == 0 {
                                v___x_4638_ = v___x_4635_;
                                v_isShared_4639_ = v_isSharedCheck_4645_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4636_);
                                crate::leanh::lean_dec(v___x_4635_);
                                v___x_4638_ = crate::leanh::lean_box(0);
                                v_isShared_4639_ = v_isSharedCheck_4645_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4635_) == 0 {
                                crate::leanh::lean_dec(v_a_4633_);
                                crate::leanh::lean_dec(v_json_4612_);
                                v_a_4646_ = crate::leanh::lean_ctor_get(v___x_4635_, 0);
                                v_isSharedCheck_4653_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4635_)) as u8;
                                if v_isSharedCheck_4653_ == 0 {
                                    v___x_4648_ = v___x_4635_;
                                    v_isShared_4649_ = v_isSharedCheck_4653_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4646_);
                                    crate::leanh::lean_dec(v___x_4635_);
                                    v___x_4648_ = crate::leanh::lean_box(0);
                                    v_isShared_4649_ = v_isSharedCheck_4653_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4654_ = crate::leanh::lean_ctor_get(v___x_4635_, 0);
                                crate::leanh::lean_inc(v_a_4654_);
                                crate::leanh::lean_dec_ref_known(v___x_4635_, 1);
                                v___x_4655_ =
                                    l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2;
                                crate::leanh::lean_inc(v_json_4612_);
                                v___x_4656_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_json_4612_, v___x_4655_);
                                if crate::leanh::lean_obj_tag(v___x_4656_) == 0 {
                                    crate::leanh::lean_dec(v_a_4654_);
                                    crate::leanh::lean_dec(v_a_4633_);
                                    crate::leanh::lean_dec(v_json_4612_);
                                    v_a_4657_ = crate::leanh::lean_ctor_get(v___x_4656_, 0);
                                    v_isSharedCheck_4666_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4656_)) as u8;
                                    if v_isSharedCheck_4666_ == 0 {
                                        v___x_4659_ = v___x_4656_;
                                        v_isShared_4660_ = v_isSharedCheck_4666_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4657_);
                                        crate::leanh::lean_dec(v___x_4656_);
                                        v___x_4659_ = crate::leanh::lean_box(0);
                                        v_isShared_4660_ = v_isSharedCheck_4666_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_4656_) == 0 {
                                        crate::leanh::lean_dec(v_a_4654_);
                                        crate::leanh::lean_dec(v_a_4633_);
                                        crate::leanh::lean_dec(v_json_4612_);
                                        v_a_4667_ = crate::leanh::lean_ctor_get(v___x_4656_, 0);
                                        v_isSharedCheck_4674_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4656_)) as u8;
                                        if v_isSharedCheck_4674_ == 0 {
                                            v___x_4669_ = v___x_4656_;
                                            v_isShared_4670_ = v_isSharedCheck_4674_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4667_);
                                            crate::leanh::lean_dec(v___x_4656_);
                                            v___x_4669_ = crate::leanh::lean_box(0);
                                            v_isShared_4670_ = v_isSharedCheck_4674_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4675_ = crate::leanh::lean_ctor_get(v___x_4656_, 0);
                                        crate::leanh::lean_inc(v_a_4675_);
                                        crate::leanh::lean_dec_ref_known(v___x_4656_, 1);
                                        v___x_4676_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3;
                                        v___x_4677_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_json_4612_, v___x_4676_);
                                        if crate::leanh::lean_obj_tag(v___x_4677_) == 0 {
                                            crate::leanh::lean_dec(v_a_4675_);
                                            crate::leanh::lean_dec(v_a_4654_);
                                            crate::leanh::lean_dec(v_a_4633_);
                                            v_a_4678_ = crate::leanh::lean_ctor_get(v___x_4677_, 0);
                                            v_isSharedCheck_4687_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4677_))
                                                    as u8;
                                            if v_isSharedCheck_4687_ == 0 {
                                                v___x_4680_ = v___x_4677_;
                                                v_isShared_4681_ = v_isSharedCheck_4687_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4678_);
                                                crate::leanh::lean_dec(v___x_4677_);
                                                v___x_4680_ = crate::leanh::lean_box(0);
                                                v_isShared_4681_ = v_isSharedCheck_4687_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_4677_) == 0 {
                                                crate::leanh::lean_dec(v_a_4675_);
                                                crate::leanh::lean_dec(v_a_4654_);
                                                crate::leanh::lean_dec(v_a_4633_);
                                                v_a_4688_ =
                                                    crate::leanh::lean_ctor_get(v___x_4677_, 0);
                                                v_isSharedCheck_4695_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4677_))
                                                        as u8;
                                                if v_isSharedCheck_4695_ == 0 {
                                                    v___x_4690_ = v___x_4677_;
                                                    v_isShared_4691_ = v_isSharedCheck_4695_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4688_);
                                                    crate::leanh::lean_dec(v___x_4677_);
                                                    v___x_4690_ = crate::leanh::lean_box(0);
                                                    v_isShared_4691_ = v_isSharedCheck_4695_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_4696_ =
                                                    crate::leanh::lean_ctor_get(v___x_4677_, 0);
                                                v_isSharedCheck_4704_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4677_))
                                                        as u8;
                                                if v_isSharedCheck_4704_ == 0 {
                                                    v___x_4698_ = v___x_4677_;
                                                    v_isShared_4699_ = v_isSharedCheck_4704_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4696_);
                                                    crate::leanh::lean_dec(v___x_4677_);
                                                    v___x_4698_ = crate::leanh::lean_box(0);
                                                    v_isShared_4699_ = v_isSharedCheck_4704_;
                                                    state = 17;
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
            1 => {
                v___x_4619_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8,
                );
                v___x_4620_ = lean_string_append(v___x_4619_, v_a_4615_);
                crate::leanh::lean_dec(v_a_4615_);
                if v_isShared_4618_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4617_, 0, v___x_4620_);
                    v___x_4622_ = v___x_4617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4623_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
                    v___x_4622_ = v_reuseFailAlloc_4623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4622_;
            }
            3 => {
                if v_isShared_4628_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4627_, 0);
                    v___x_4630_ = v___x_4627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4630_;
            }
            5 => {
                v___x_4640_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13,
                );
                v___x_4641_ = lean_string_append(v___x_4640_, v_a_4636_);
                crate::leanh::lean_dec(v_a_4636_);
                if v_isShared_4639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4638_, 0, v___x_4641_);
                    v___x_4643_ = v___x_4638_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4641_);
                    v___x_4643_ = v_reuseFailAlloc_4644_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4643_;
            }
            7 => {
                if v_isShared_4649_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4648_, 0);
                    v___x_4651_ = v___x_4648_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
                    v___x_4651_ = v_reuseFailAlloc_4652_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4651_;
            }
            9 => {
                v___x_4661_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18,
                );
                v___x_4662_ = lean_string_append(v___x_4661_, v_a_4657_);
                crate::leanh::lean_dec(v_a_4657_);
                if v_isShared_4660_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4659_, 0, v___x_4662_);
                    v___x_4664_ = v___x_4659_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
                    v___x_4664_ = v_reuseFailAlloc_4665_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4664_;
            }
            11 => {
                if v_isShared_4670_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4669_, 0);
                    v___x_4672_ = v___x_4669_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
                    v___x_4672_ = v_reuseFailAlloc_4673_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4672_;
            }
            13 => {
                v___x_4682_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23,
                );
                v___x_4683_ = lean_string_append(v___x_4682_, v_a_4678_);
                crate::leanh::lean_dec(v_a_4678_);
                if v_isShared_4681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4683_);
                    v___x_4685_ = v___x_4680_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4683_);
                    v___x_4685_ = v_reuseFailAlloc_4686_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4685_;
            }
            15 => {
                if v_isShared_4691_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4690_, 0);
                    v___x_4693_ = v___x_4690_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
                    v___x_4693_ = v_reuseFailAlloc_4694_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4693_;
            }
            17 => {
                v___x_4700_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4700_, 0, v_a_4633_);
                crate::leanh::lean_ctor_set(v___x_4700_, 1, v_a_4654_);
                crate::leanh::lean_ctor_set(v___x_4700_, 2, v_a_4675_);
                crate::leanh::lean_ctor_set(v___x_4700_, 3, v_a_4696_);
                if v_isShared_4699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4698_, 0, v___x_4700_);
                    v___x_4702_ = v___x_4698_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4700_);
                    v___x_4702_ = v_reuseFailAlloc_4703_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4702_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(
    mut v_c_4707_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lean_x3f_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lean_x3f_4708_ = crate::leanh::lean_ctor_get(v_c_4707_, 3);
    if crate::leanh::lean_obj_tag(v_lean_x3f_4708_) == 1 {
        let mut v_val_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_incrementalDiagnosticSupport_x3f_4710_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        v_val_4709_ = crate::leanh::lean_ctor_get(v_lean_x3f_4708_, 0);
        v_incrementalDiagnosticSupport_x3f_4710_ = crate::leanh::lean_ctor_get(v_val_4709_, 0);
        if crate::leanh::lean_obj_tag(v_incrementalDiagnosticSupport_x3f_4710_) == 1 {
            let mut v_val_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4712_: u8 = 0;
            v_val_4711_ = crate::leanh::lean_ctor_get(v_incrementalDiagnosticSupport_x3f_4710_, 0);
            v___x_4712_ = (crate::leanh::lean_unbox(v_val_4711_) as u8);
            return v___x_4712_;
        } else {
            let mut v___x_4713_: u8 = 0;
            v___x_4713_ = 0;
            return v___x_4713_;
        }
    } else {
        let mut v___x_4714_: u8 = 0;
        v___x_4714_ = 0;
        return v___x_4714_;
    }
}
pub unsafe fn l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport___boxed(
    mut v_c_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4716_: u8 = 0;
    let mut v_r_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4716_ = l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(v_c_4715_);
    crate::leanh::lean_dec_ref(v_c_4715_);
    v_r_4717_ = crate::leanh::lean_box((v_res_4716_) as usize);
    return v_r_4717_;
}
pub unsafe fn l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(
    mut v_c_4718_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lean_x3f_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lean_x3f_4719_ = crate::leanh::lean_ctor_get(v_c_4718_, 3);
    if crate::leanh::lean_obj_tag(v_lean_x3f_4719_) == 1 {
        let mut v_val_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_silentDiagnosticSupport_x3f_4721_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        v_val_4720_ = crate::leanh::lean_ctor_get(v_lean_x3f_4719_, 0);
        v_silentDiagnosticSupport_x3f_4721_ = crate::leanh::lean_ctor_get(v_val_4720_, 1);
        if crate::leanh::lean_obj_tag(v_silentDiagnosticSupport_x3f_4721_) == 1 {
            let mut v_val_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4723_: u8 = 0;
            v_val_4722_ = crate::leanh::lean_ctor_get(v_silentDiagnosticSupport_x3f_4721_, 0);
            v___x_4723_ = (crate::leanh::lean_unbox(v_val_4722_) as u8);
            return v___x_4723_;
        } else {
            let mut v___x_4724_: u8 = 0;
            v___x_4724_ = 0;
            return v___x_4724_;
        }
    } else {
        let mut v___x_4725_: u8 = 0;
        v___x_4725_ = 0;
        return v___x_4725_;
    }
}
pub unsafe fn l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport___boxed(
    mut v_c_4726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4727_: u8 = 0;
    let mut v_r_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4727_ = l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(v_c_4726_);
    crate::leanh::lean_dec_ref(v_c_4726_);
    v_r_4728_ = crate::leanh::lean_box((v_res_4727_) as usize);
    return v_r_4728_;
}
pub unsafe fn l_Lean_Lsp_ClientCapabilities_rpcWireFormat(
    mut v_c_4729_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lean_x3f_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lean_x3f_4730_ = crate::leanh::lean_ctor_get(v_c_4729_, 3);
    if crate::leanh::lean_obj_tag(v_lean_x3f_4730_) == 1 {
        let mut v_val_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rpcWireFormat_x3f_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4731_ = crate::leanh::lean_ctor_get(v_lean_x3f_4730_, 0);
        v_rpcWireFormat_x3f_4732_ = crate::leanh::lean_ctor_get(v_val_4731_, 2);
        if crate::leanh::lean_obj_tag(v_rpcWireFormat_x3f_4732_) == 1 {
            let mut v_val_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4734_: u8 = 0;
            v_val_4733_ = crate::leanh::lean_ctor_get(v_rpcWireFormat_x3f_4732_, 0);
            v___x_4734_ = (crate::leanh::lean_unbox(v_val_4733_) as u8);
            return v___x_4734_;
        } else {
            let mut v___x_4735_: u8 = 0;
            v___x_4735_ = 0;
            return v___x_4735_;
        }
    } else {
        let mut v___x_4736_: u8 = 0;
        v___x_4736_ = 0;
        return v___x_4736_;
    }
}
pub unsafe fn l_Lean_Lsp_ClientCapabilities_rpcWireFormat___boxed(
    mut v_c_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: u8 = 0;
    let mut v_r_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_Lsp_ClientCapabilities_rpcWireFormat(v_c_4737_);
    crate::leanh::lean_dec_ref(v_c_4737_);
    v_r_4739_ = crate::leanh::lean_box((v_res_4738_) as usize);
    return v_r_4739_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(
    mut v_x_4742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4742_) == 0 {
                    v___x_4743_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4743_;
                } else {
                    v___x_4744_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(v_x_4742_);
                    if crate::leanh::lean_obj_tag(v___x_4744_) == 0 {
                        v_a_4745_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4752_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4752_ == 0 {
                            v___x_4747_ = v___x_4744_;
                            v_isShared_4748_ = v_isSharedCheck_4752_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4745_);
                            crate::leanh::lean_dec(v___x_4744_);
                            v___x_4747_ = crate::leanh::lean_box(0);
                            v_isShared_4748_ = v_isSharedCheck_4752_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4761_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4761_ == 0 {
                            v___x_4755_ = v___x_4744_;
                            v_isShared_4756_ = v_isSharedCheck_4761_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4753_);
                            crate::leanh::lean_dec(v___x_4744_);
                            v___x_4755_ = crate::leanh::lean_box(0);
                            v_isShared_4756_ = v_isSharedCheck_4761_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4748_ == 0 {
                    v___x_4750_ = v___x_4747_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
                    v___x_4750_ = v_reuseFailAlloc_4751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4750_;
            }
            3 => {
                v___x_4757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4757_, 0, v_a_4753_);
                if v_isShared_4756_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4755_, 0, v___x_4757_);
                    v___x_4759_ = v___x_4755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4757_);
                    v___x_4759_ = v_reuseFailAlloc_4760_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___boxed(
    mut v_x_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v_x_4762_);
    crate::leanh::lean_dec(v_x_4762_);
    return v_res_4763_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(
    mut v_j_4764_: *mut crate::leanh::LeanObject,
    mut v_k_4765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4766_ = l_Lean_Json_getObjValD(v_j_4764_, v_k_4765_);
    v___x_4767_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v___x_4766_);
    crate::leanh::lean_dec(v___x_4766_);
    return v___x_4767_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0___boxed(
    mut v_j_4768_: *mut crate::leanh::LeanObject,
    mut v_k_4769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4770_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_j_4768_, v_k_4769_);
    crate::leanh::lean_dec_ref(v_k_4769_);
    return v_res_4770_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(
    mut v_x_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4779_: u8 = 0;
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4783_: u8 = 0;
    let mut v_a_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4773_) == 0 {
                    v___x_4774_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0;
                    return v___x_4774_;
                } else {
                    v___x_4775_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson(v_x_4773_);
                    if crate::leanh::lean_obj_tag(v___x_4775_) == 0 {
                        v_a_4776_ = crate::leanh::lean_ctor_get(v___x_4775_, 0);
                        v_isSharedCheck_4783_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4775_)) as u8;
                        if v_isSharedCheck_4783_ == 0 {
                            v___x_4778_ = v___x_4775_;
                            v_isShared_4779_ = v_isSharedCheck_4783_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4776_);
                            crate::leanh::lean_dec(v___x_4775_);
                            v___x_4778_ = crate::leanh::lean_box(0);
                            v_isShared_4779_ = v_isSharedCheck_4783_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4784_ = crate::leanh::lean_ctor_get(v___x_4775_, 0);
                        v_isSharedCheck_4792_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4775_)) as u8;
                        if v_isSharedCheck_4792_ == 0 {
                            v___x_4786_ = v___x_4775_;
                            v_isShared_4787_ = v_isSharedCheck_4792_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4784_);
                            crate::leanh::lean_dec(v___x_4775_);
                            v___x_4786_ = crate::leanh::lean_box(0);
                            v_isShared_4787_ = v_isSharedCheck_4792_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4779_ == 0 {
                    v___x_4781_ = v___x_4778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
                    v___x_4781_ = v_reuseFailAlloc_4782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4781_;
            }
            3 => {
                v___x_4788_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4788_, 0, v_a_4784_);
                if v_isShared_4787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4786_, 0, v___x_4788_);
                    v___x_4790_ = v___x_4786_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
                    v___x_4790_ = v_reuseFailAlloc_4791_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(
    mut v_j_4793_: *mut crate::leanh::LeanObject,
    mut v_k_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = l_Lean_Json_getObjValD(v_j_4793_, v_k_4794_);
    v___x_4796_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(v___x_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1___boxed(
    mut v_j_4797_: *mut crate::leanh::LeanObject,
    mut v_k_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4799_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_j_4797_, v_k_4798_);
    crate::leanh::lean_dec_ref(v_k_4798_);
    return v_res_4799_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = 1;
    v___x_4807_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2;
    v___x_4808_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4807_, v___x_4806_);
    return v___x_4808_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4809_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_4810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3,
    );
    v___x_4811_ = lean_string_append(v___x_4810_, v___x_4809_);
    return v___x_4811_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4815_ = 1;
    v___x_4816_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6;
    v___x_4817_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4816_, v___x_4815_);
    return v___x_4817_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7,
    );
    v___x_4819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4,
    );
    v___x_4820_ = lean_string_append(v___x_4819_, v___x_4818_);
    return v___x_4820_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4821_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8,
    );
    v___x_4823_ = lean_string_append(v___x_4822_, v___x_4821_);
    return v___x_4823_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: u8 = 0;
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = 1;
    v___x_4829_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12;
    v___x_4830_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4829_, v___x_4828_);
    return v___x_4830_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13,
    );
    v___x_4832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4,
    );
    v___x_4833_ = lean_string_append(v___x_4832_, v___x_4831_);
    return v___x_4833_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_4835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14,
    );
    v___x_4836_ = lean_string_append(v___x_4835_, v___x_4834_);
    return v___x_4836_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(
    mut v_json_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4843_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut v_a_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v_a_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4878_: u8 = 0;
    let mut v_a_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4882_: u8 = 0;
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4838_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0;
                crate::leanh::lean_inc(v_json_4837_);
                v___x_4839_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_json_4837_, v___x_4838_);
                if crate::leanh::lean_obj_tag(v___x_4839_) == 0 {
                    crate::leanh::lean_dec(v_json_4837_);
                    v_a_4840_ = crate::leanh::lean_ctor_get(v___x_4839_, 0);
                    v_isSharedCheck_4849_ = (!crate::leanh::lean_is_exclusive(v___x_4839_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4842_ = v___x_4839_;
                        v_isShared_4843_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4840_);
                        crate::leanh::lean_dec(v___x_4839_);
                        v___x_4842_ = crate::leanh::lean_box(0);
                        v_isShared_4843_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4839_) == 0 {
                        crate::leanh::lean_dec(v_json_4837_);
                        v_a_4850_ = crate::leanh::lean_ctor_get(v___x_4839_, 0);
                        v_isSharedCheck_4857_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4839_)) as u8;
                        if v_isSharedCheck_4857_ == 0 {
                            v___x_4852_ = v___x_4839_;
                            v_isShared_4853_ = v_isSharedCheck_4857_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4850_);
                            crate::leanh::lean_dec(v___x_4839_);
                            v___x_4852_ = crate::leanh::lean_box(0);
                            v_isShared_4853_ = v_isSharedCheck_4857_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4858_ = crate::leanh::lean_ctor_get(v___x_4839_, 0);
                        crate::leanh::lean_inc(v_a_4858_);
                        crate::leanh::lean_dec_ref_known(v___x_4839_, 1);
                        v___x_4859_ =
                            l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10;
                        v___x_4860_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_json_4837_, v___x_4859_);
                        if crate::leanh::lean_obj_tag(v___x_4860_) == 0 {
                            crate::leanh::lean_dec(v_a_4858_);
                            v_a_4861_ = crate::leanh::lean_ctor_get(v___x_4860_, 0);
                            v_isSharedCheck_4870_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4860_)) as u8;
                            if v_isSharedCheck_4870_ == 0 {
                                v___x_4863_ = v___x_4860_;
                                v_isShared_4864_ = v_isSharedCheck_4870_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4861_);
                                crate::leanh::lean_dec(v___x_4860_);
                                v___x_4863_ = crate::leanh::lean_box(0);
                                v_isShared_4864_ = v_isSharedCheck_4870_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4860_) == 0 {
                                crate::leanh::lean_dec(v_a_4858_);
                                v_a_4871_ = crate::leanh::lean_ctor_get(v___x_4860_, 0);
                                v_isSharedCheck_4878_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4860_)) as u8;
                                if v_isSharedCheck_4878_ == 0 {
                                    v___x_4873_ = v___x_4860_;
                                    v_isShared_4874_ = v_isSharedCheck_4878_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4871_);
                                    crate::leanh::lean_dec(v___x_4860_);
                                    v___x_4873_ = crate::leanh::lean_box(0);
                                    v_isShared_4874_ = v_isSharedCheck_4878_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4879_ = crate::leanh::lean_ctor_get(v___x_4860_, 0);
                                v_isSharedCheck_4887_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4860_)) as u8;
                                if v_isSharedCheck_4887_ == 0 {
                                    v___x_4881_ = v___x_4860_;
                                    v_isShared_4882_ = v_isSharedCheck_4887_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4879_);
                                    crate::leanh::lean_dec(v___x_4860_);
                                    v___x_4881_ = crate::leanh::lean_box(0);
                                    v_isShared_4882_ = v_isSharedCheck_4887_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4844_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9,
                );
                v___x_4845_ = lean_string_append(v___x_4844_, v_a_4840_);
                crate::leanh::lean_dec(v_a_4840_);
                if v_isShared_4843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4842_, 0, v___x_4845_);
                    v___x_4847_ = v___x_4842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
                    v___x_4847_ = v_reuseFailAlloc_4848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4847_;
            }
            3 => {
                if v_isShared_4853_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4852_, 0);
                    v___x_4855_ = v___x_4852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4856_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
                    v___x_4855_ = v_reuseFailAlloc_4856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4855_;
            }
            5 => {
                v___x_4865_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15,
                );
                v___x_4866_ = lean_string_append(v___x_4865_, v_a_4861_);
                crate::leanh::lean_dec(v_a_4861_);
                if v_isShared_4864_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4863_, 0, v___x_4866_);
                    v___x_4868_ = v___x_4863_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4869_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4866_);
                    v___x_4868_ = v_reuseFailAlloc_4869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4868_;
            }
            7 => {
                if v_isShared_4874_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4873_, 0);
                    v___x_4876_ = v___x_4873_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
                    v___x_4876_ = v_reuseFailAlloc_4877_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4876_;
            }
            9 => {
                v___x_4883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4883_, 0, v_a_4858_);
                crate::leanh::lean_ctor_set(v___x_4883_, 1, v_a_4879_);
                if v_isShared_4882_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4881_, 0, v___x_4883_);
                    v___x_4885_ = v___x_4881_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
                    v___x_4885_ = v_reuseFailAlloc_4886_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(
    mut v_k_4890_: *mut crate::leanh::LeanObject,
    mut v_x_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4891_) == 0 {
        let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4890_);
        v___x_4892_ = crate::leanh::lean_box(0);
        return v___x_4892_;
    } else {
        let mut v_val_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4893_ = crate::leanh::lean_ctor_get(v_x_4891_, 0);
        crate::leanh::lean_inc(v_val_4893_);
        crate::leanh::lean_dec_ref_known(v_x_4891_, 1);
        v___x_4894_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(v_val_4893_);
        v___x_4895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4895_, 0, v_k_4890_);
        crate::leanh::lean_ctor_set(v___x_4895_, 1, v___x_4894_);
        v___x_4896_ = crate::leanh::lean_box(0);
        v___x_4897_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4897_, 0, v___x_4895_);
        crate::leanh::lean_ctor_set(v___x_4897_, 1, v___x_4896_);
        return v___x_4897_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(
    mut v_k_4898_: *mut crate::leanh::LeanObject,
    mut v_x_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4899_) == 0 {
        let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4898_);
        v___x_4900_ = crate::leanh::lean_box(0);
        return v___x_4900_;
    } else {
        let mut v_val_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4901_ = crate::leanh::lean_ctor_get(v_x_4899_, 0);
        crate::leanh::lean_inc(v_val_4901_);
        crate::leanh::lean_dec_ref_known(v_x_4899_, 1);
        v___x_4902_ = l_Lean_Lsp_instToJsonRpcOptions_toJson(v_val_4901_);
        v___x_4903_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4903_, 0, v_k_4898_);
        crate::leanh::lean_ctor_set(v___x_4903_, 1, v___x_4902_);
        v___x_4904_ = crate::leanh::lean_box(0);
        v___x_4905_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4905_, 0, v___x_4903_);
        crate::leanh::lean_ctor_set(v___x_4905_, 1, v___x_4904_);
        return v___x_4905_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(
    mut v_x_4906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_moduleHierarchyProvider_x3f_4907_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_rpcProvider_x3f_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4911_: u8 = 0;
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_moduleHierarchyProvider_x3f_4907_ = crate::leanh::lean_ctor_get(v_x_4906_, 0);
                v_rpcProvider_x3f_4908_ = crate::leanh::lean_ctor_get(v_x_4906_, 1);
                v_isSharedCheck_4924_ = (!crate::leanh::lean_is_exclusive(v_x_4906_)) as u8;
                if v_isSharedCheck_4924_ == 0 {
                    v___x_4910_ = v_x_4906_;
                    v_isShared_4911_ = v_isSharedCheck_4924_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rpcProvider_x3f_4908_);
                    crate::leanh::lean_inc(v_moduleHierarchyProvider_x3f_4907_);
                    crate::leanh::lean_dec(v_x_4906_);
                    v___x_4910_ = crate::leanh::lean_box(0);
                    v_isShared_4911_ = v_isSharedCheck_4924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4912_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0;
                v___x_4913_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v___x_4912_, v_moduleHierarchyProvider_x3f_4907_);
                v___x_4914_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10;
                v___x_4915_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(v___x_4914_, v_rpcProvider_x3f_4908_);
                v___x_4916_ = crate::leanh::lean_box(0);
                if v_isShared_4911_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4910_, 1);
                    crate::leanh::lean_ctor_set(v___x_4910_, 1, v___x_4916_);
                    crate::leanh::lean_ctor_set(v___x_4910_, 0, v___x_4915_);
                    v___x_4918_ = v___x_4910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4923_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 1, v___x_4916_);
                    v___x_4918_ = v_reuseFailAlloc_4923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4919_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4919_, 0, v___x_4913_);
                crate::leanh::lean_ctor_set(v___x_4919_, 1, v___x_4918_);
                v___x_4920_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
                v___x_4921_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_4919_, v___x_4920_);
                v___x_4922_ = l_Lean_Json_mkObj(v___x_4921_);
                crate::leanh::lean_dec(v___x_4921_);
                return v___x_4922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(
    mut v_k_4927_: *mut crate::leanh::LeanObject,
    mut v_x_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4928_) == 0 {
        let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4927_);
        v___x_4929_ = crate::leanh::lean_box(0);
        return v___x_4929_;
    } else {
        let mut v_val_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4930_ = crate::leanh::lean_ctor_get(v_x_4928_, 0);
        v___x_4931_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_val_4930_);
        v___x_4932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4932_, 0, v_k_4927_);
        crate::leanh::lean_ctor_set(v___x_4932_, 1, v___x_4931_);
        v___x_4933_ = crate::leanh::lean_box(0);
        v___x_4934_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4934_, 0, v___x_4932_);
        crate::leanh::lean_ctor_set(v___x_4934_, 1, v___x_4933_);
        return v___x_4934_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0___boxed(
    mut v_k_4935_: *mut crate::leanh::LeanObject,
    mut v_x_4936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4937_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(
        v_k_4935_, v_x_4936_,
    );
    crate::leanh::lean_dec(v_x_4936_);
    return v_res_4937_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(
    mut v_k_4938_: *mut crate::leanh::LeanObject,
    mut v_x_4939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4939_) == 0 {
        let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4938_);
        v___x_4940_ = crate::leanh::lean_box(0);
        return v___x_4940_;
    } else {
        let mut v_val_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4941_ = crate::leanh::lean_ctor_get(v_x_4939_, 0);
        crate::leanh::lean_inc(v_val_4941_);
        crate::leanh::lean_dec_ref_known(v_x_4939_, 1);
        v___x_4942_ = l_Lean_Lsp_instToJsonCompletionOptions_toJson(v_val_4941_);
        v___x_4943_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4943_, 0, v_k_4938_);
        crate::leanh::lean_ctor_set(v___x_4943_, 1, v___x_4942_);
        v___x_4944_ = crate::leanh::lean_box(0);
        v___x_4945_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4943_);
        crate::leanh::lean_ctor_set(v___x_4945_, 1, v___x_4944_);
        return v___x_4945_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(
    mut v_k_4946_: *mut crate::leanh::LeanObject,
    mut v_x_4947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4947_) == 0 {
        let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4946_);
        v___x_4948_ = crate::leanh::lean_box(0);
        return v___x_4948_;
    } else {
        let mut v_val_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4950_: u8 = 0;
        let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4949_ = crate::leanh::lean_ctor_get(v_x_4947_, 0);
        v___x_4950_ = (crate::leanh::lean_unbox(v_val_4949_) as u8);
        v___x_4951_ = l_Lean_Lsp_instToJsonRenameOptions_toJson(v___x_4950_);
        v___x_4952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4952_, 0, v_k_4946_);
        crate::leanh::lean_ctor_set(v___x_4952_, 1, v___x_4951_);
        v___x_4953_ = crate::leanh::lean_box(0);
        v___x_4954_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4954_, 0, v___x_4952_);
        crate::leanh::lean_ctor_set(v___x_4954_, 1, v___x_4953_);
        return v___x_4954_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2___boxed(
    mut v_k_4955_: *mut crate::leanh::LeanObject,
    mut v_x_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(
        v_k_4955_, v_x_4956_,
    );
    crate::leanh::lean_dec(v_x_4956_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(
    mut v_k_4958_: *mut crate::leanh::LeanObject,
    mut v_x_4959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4959_) == 0 {
        let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4958_);
        v___x_4960_ = crate::leanh::lean_box(0);
        return v___x_4960_;
    } else {
        let mut v_val_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4961_ = crate::leanh::lean_ctor_get(v_x_4959_, 0);
        crate::leanh::lean_inc(v_val_4961_);
        crate::leanh::lean_dec_ref_known(v_x_4959_, 1);
        v___x_4962_ = l_Lean_Lsp_instToJsonSemanticTokensOptions_toJson(v_val_4961_);
        v___x_4963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4963_, 0, v_k_4958_);
        crate::leanh::lean_ctor_set(v___x_4963_, 1, v___x_4962_);
        v___x_4964_ = crate::leanh::lean_box(0);
        v___x_4965_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4965_, 0, v___x_4963_);
        crate::leanh::lean_ctor_set(v___x_4965_, 1, v___x_4964_);
        return v___x_4965_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(
    mut v_k_4966_: *mut crate::leanh::LeanObject,
    mut v_x_4967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4967_) == 0 {
        let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4966_);
        v___x_4968_ = crate::leanh::lean_box(0);
        return v___x_4968_;
    } else {
        let mut v_val_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4969_ = crate::leanh::lean_ctor_get(v_x_4967_, 0);
        crate::leanh::lean_inc(v_val_4969_);
        crate::leanh::lean_dec_ref_known(v_x_4967_, 1);
        v___x_4970_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson(v_val_4969_);
        v___x_4971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4971_, 0, v_k_4966_);
        crate::leanh::lean_ctor_set(v___x_4971_, 1, v___x_4970_);
        v___x_4972_ = crate::leanh::lean_box(0);
        v___x_4973_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4973_, 0, v___x_4971_);
        crate::leanh::lean_ctor_set(v___x_4973_, 1, v___x_4972_);
        return v___x_4973_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(
    mut v_k_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4975_) == 0 {
        let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4974_);
        v___x_4976_ = crate::leanh::lean_box(0);
        return v___x_4976_;
    } else {
        let mut v_val_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4977_ = crate::leanh::lean_ctor_get(v_x_4975_, 0);
        v___x_4978_ = l_Lean_Lsp_instToJsonInlayHintOptions_toJson(v_val_4977_);
        v___x_4979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4979_, 0, v_k_4974_);
        crate::leanh::lean_ctor_set(v___x_4979_, 1, v___x_4978_);
        v___x_4980_ = crate::leanh::lean_box(0);
        v___x_4981_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4981_, 0, v___x_4979_);
        crate::leanh::lean_ctor_set(v___x_4981_, 1, v___x_4980_);
        return v___x_4981_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5___boxed(
    mut v_k_4982_: *mut crate::leanh::LeanObject,
    mut v_x_4983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4984_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(
        v_k_4982_, v_x_4983_,
    );
    crate::leanh::lean_dec(v_x_4983_);
    return v_res_4984_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(
    mut v_k_4985_: *mut crate::leanh::LeanObject,
    mut v_x_4986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4986_) == 0 {
        let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4985_);
        v___x_4987_ = crate::leanh::lean_box(0);
        return v___x_4987_;
    } else {
        let mut v_val_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4988_ = crate::leanh::lean_ctor_get(v_x_4986_, 0);
        crate::leanh::lean_inc(v_val_4988_);
        crate::leanh::lean_dec_ref_known(v_x_4986_, 1);
        v___x_4989_ = l_Lean_Lsp_instToJsonSignatureHelpOptions_toJson(v_val_4988_);
        v___x_4990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4990_, 0, v_k_4985_);
        crate::leanh::lean_ctor_set(v___x_4990_, 1, v___x_4989_);
        v___x_4991_ = crate::leanh::lean_box(0);
        v___x_4992_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4992_, 0, v___x_4990_);
        crate::leanh::lean_ctor_set(v___x_4992_, 1, v___x_4991_);
        return v___x_4992_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(
    mut v_k_4993_: *mut crate::leanh::LeanObject,
    mut v_x_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4994_) == 0 {
        let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4993_);
        v___x_4995_ = crate::leanh::lean_box(0);
        return v___x_4995_;
    } else {
        let mut v_val_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4997_: u8 = 0;
        let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4996_ = crate::leanh::lean_ctor_get(v_x_4994_, 0);
        v___x_4997_ = (crate::leanh::lean_unbox(v_val_4996_) as u8);
        v___x_4998_ = l_Lean_Lsp_instToJsonDocumentColorOptions_toJson(v___x_4997_);
        v___x_4999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4999_, 0, v_k_4993_);
        crate::leanh::lean_ctor_set(v___x_4999_, 1, v___x_4998_);
        v___x_5000_ = crate::leanh::lean_box(0);
        v___x_5001_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5001_, 0, v___x_4999_);
        crate::leanh::lean_ctor_set(v___x_5001_, 1, v___x_5000_);
        return v___x_5001_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7___boxed(
    mut v_k_5002_: *mut crate::leanh::LeanObject,
    mut v_x_5003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5004_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(
        v_k_5002_, v_x_5003_,
    );
    crate::leanh::lean_dec(v_x_5003_);
    return v_res_5004_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(
    mut v_k_5005_: *mut crate::leanh::LeanObject,
    mut v_x_5006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5006_) == 0 {
        let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_5005_);
        v___x_5007_ = crate::leanh::lean_box(0);
        return v___x_5007_;
    } else {
        let mut v_val_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5008_ = crate::leanh::lean_ctor_get(v_x_5006_, 0);
        crate::leanh::lean_inc(v_val_5008_);
        crate::leanh::lean_dec_ref_known(v_x_5006_, 1);
        v___x_5009_ = l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(v_val_5008_);
        v___x_5010_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5010_, 0, v_k_5005_);
        crate::leanh::lean_ctor_set(v___x_5010_, 1, v___x_5009_);
        v___x_5011_ = crate::leanh::lean_box(0);
        v___x_5012_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5012_, 0, v___x_5010_);
        crate::leanh::lean_ctor_set(v___x_5012_, 1, v___x_5011_);
        return v___x_5012_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonServerCapabilities_toJson(
    mut v_x_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocumentSync_x3f_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_completionProvider_x3f_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hoverProvider_5035_: u8 = 0;
    let mut v_documentHighlightProvider_5036_: u8 = 0;
    let mut v_documentSymbolProvider_5037_: u8 = 0;
    let mut v_definitionProvider_5038_: u8 = 0;
    let mut v_declarationProvider_5039_: u8 = 0;
    let mut v_typeDefinitionProvider_5040_: u8 = 0;
    let mut v_referencesProvider_5041_: u8 = 0;
    let mut v_callHierarchyProvider_5042_: u8 = 0;
    let mut v_renameProvider_x3f_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_workspaceSymbolProvider_5044_: u8 = 0;
    let mut v_foldingRangeProvider_5045_: u8 = 0;
    let mut v_semanticTokensProvider_x3f_5046_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_codeActionProvider_x3f_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlayHintProvider_x3f_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_signatureHelpProvider_x3f_5049_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_colorProvider_x3f_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_experimental_x3f_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocumentSync_x3f_5033_ = crate::leanh::lean_ctor_get(v_x_5032_, 0);
    crate::leanh::lean_inc(v_textDocumentSync_x3f_5033_);
    v_completionProvider_x3f_5034_ = crate::leanh::lean_ctor_get(v_x_5032_, 1);
    crate::leanh::lean_inc(v_completionProvider_x3f_5034_);
    v_hoverProvider_5035_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
    );
    v_documentHighlightProvider_5036_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
    );
    v_documentSymbolProvider_5037_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
    );
    v_definitionProvider_5038_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 3) as u32,
    );
    v_declarationProvider_5039_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 4) as u32,
    );
    v_typeDefinitionProvider_5040_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 5) as u32,
    );
    v_referencesProvider_5041_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 6) as u32,
    );
    v_callHierarchyProvider_5042_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 7) as u32,
    );
    v_renameProvider_x3f_5043_ = crate::leanh::lean_ctor_get(v_x_5032_, 2);
    crate::leanh::lean_inc(v_renameProvider_x3f_5043_);
    v_workspaceSymbolProvider_5044_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 8) as u32,
    );
    v_foldingRangeProvider_5045_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 9) as u32,
    );
    v_semanticTokensProvider_x3f_5046_ = crate::leanh::lean_ctor_get(v_x_5032_, 3);
    crate::leanh::lean_inc(v_semanticTokensProvider_x3f_5046_);
    v_codeActionProvider_x3f_5047_ = crate::leanh::lean_ctor_get(v_x_5032_, 4);
    crate::leanh::lean_inc(v_codeActionProvider_x3f_5047_);
    v_inlayHintProvider_x3f_5048_ = crate::leanh::lean_ctor_get(v_x_5032_, 5);
    crate::leanh::lean_inc(v_inlayHintProvider_x3f_5048_);
    v_signatureHelpProvider_x3f_5049_ = crate::leanh::lean_ctor_get(v_x_5032_, 6);
    crate::leanh::lean_inc(v_signatureHelpProvider_x3f_5049_);
    v_colorProvider_x3f_5050_ = crate::leanh::lean_ctor_get(v_x_5032_, 7);
    crate::leanh::lean_inc(v_colorProvider_x3f_5050_);
    v_experimental_x3f_5051_ = crate::leanh::lean_ctor_get(v_x_5032_, 8);
    crate::leanh::lean_inc(v_experimental_x3f_5051_);
    crate::leanh::lean_dec_ref(v_x_5032_);
    v___x_5052_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0;
    v___x_5053_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(
        v___x_5052_,
        v_textDocumentSync_x3f_5033_,
    );
    crate::leanh::lean_dec(v_textDocumentSync_x3f_5033_);
    v___x_5054_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1;
    v___x_5055_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(
        v___x_5054_,
        v_completionProvider_x3f_5034_,
    );
    v___x_5056_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2;
    v___x_5057_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5057_, 0 as u32, v_hoverProvider_5035_);
    v___x_5058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5058_, 0, v___x_5056_);
    crate::leanh::lean_ctor_set(v___x_5058_, 1, v___x_5057_);
    v___x_5059_ = crate::leanh::lean_box(0);
    v___x_5060_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5060_, 0, v___x_5058_);
    crate::leanh::lean_ctor_set(v___x_5060_, 1, v___x_5059_);
    v___x_5061_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3;
    v___x_5062_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5062_, 0 as u32, v_documentHighlightProvider_5036_);
    v___x_5063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5063_, 0, v___x_5061_);
    crate::leanh::lean_ctor_set(v___x_5063_, 1, v___x_5062_);
    v___x_5064_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5064_, 0, v___x_5063_);
    crate::leanh::lean_ctor_set(v___x_5064_, 1, v___x_5059_);
    v___x_5065_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4;
    v___x_5066_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5066_, 0 as u32, v_documentSymbolProvider_5037_);
    v___x_5067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5067_, 0, v___x_5065_);
    crate::leanh::lean_ctor_set(v___x_5067_, 1, v___x_5066_);
    v___x_5068_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5068_, 0, v___x_5067_);
    crate::leanh::lean_ctor_set(v___x_5068_, 1, v___x_5059_);
    v___x_5069_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5;
    v___x_5070_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5070_, 0 as u32, v_definitionProvider_5038_);
    v___x_5071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5071_, 0, v___x_5069_);
    crate::leanh::lean_ctor_set(v___x_5071_, 1, v___x_5070_);
    v___x_5072_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5072_, 0, v___x_5071_);
    crate::leanh::lean_ctor_set(v___x_5072_, 1, v___x_5059_);
    v___x_5073_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6;
    v___x_5074_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5074_, 0 as u32, v_declarationProvider_5039_);
    v___x_5075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5075_, 0, v___x_5073_);
    crate::leanh::lean_ctor_set(v___x_5075_, 1, v___x_5074_);
    v___x_5076_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5076_, 0, v___x_5075_);
    crate::leanh::lean_ctor_set(v___x_5076_, 1, v___x_5059_);
    v___x_5077_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7;
    v___x_5078_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5078_, 0 as u32, v_typeDefinitionProvider_5040_);
    v___x_5079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5079_, 0, v___x_5077_);
    crate::leanh::lean_ctor_set(v___x_5079_, 1, v___x_5078_);
    v___x_5080_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5080_, 0, v___x_5079_);
    crate::leanh::lean_ctor_set(v___x_5080_, 1, v___x_5059_);
    v___x_5081_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8;
    v___x_5082_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5082_, 0 as u32, v_referencesProvider_5041_);
    v___x_5083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5083_, 0, v___x_5081_);
    crate::leanh::lean_ctor_set(v___x_5083_, 1, v___x_5082_);
    v___x_5084_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5084_, 0, v___x_5083_);
    crate::leanh::lean_ctor_set(v___x_5084_, 1, v___x_5059_);
    v___x_5085_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9;
    v___x_5086_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5086_, 0 as u32, v_callHierarchyProvider_5042_);
    v___x_5087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5087_, 0, v___x_5085_);
    crate::leanh::lean_ctor_set(v___x_5087_, 1, v___x_5086_);
    v___x_5088_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5088_, 0, v___x_5087_);
    crate::leanh::lean_ctor_set(v___x_5088_, 1, v___x_5059_);
    v___x_5089_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10;
    v___x_5090_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(
        v___x_5089_,
        v_renameProvider_x3f_5043_,
    );
    crate::leanh::lean_dec(v_renameProvider_x3f_5043_);
    v___x_5091_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11;
    v___x_5092_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5092_, 0 as u32, v_workspaceSymbolProvider_5044_);
    v___x_5093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5093_, 0, v___x_5091_);
    crate::leanh::lean_ctor_set(v___x_5093_, 1, v___x_5092_);
    v___x_5094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5094_, 0, v___x_5093_);
    crate::leanh::lean_ctor_set(v___x_5094_, 1, v___x_5059_);
    v___x_5095_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12;
    v___x_5096_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5096_, 0 as u32, v_foldingRangeProvider_5045_);
    v___x_5097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5097_, 0, v___x_5095_);
    crate::leanh::lean_ctor_set(v___x_5097_, 1, v___x_5096_);
    v___x_5098_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5098_, 0, v___x_5097_);
    crate::leanh::lean_ctor_set(v___x_5098_, 1, v___x_5059_);
    v___x_5099_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13;
    v___x_5100_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(
        v___x_5099_,
        v_semanticTokensProvider_x3f_5046_,
    );
    v___x_5101_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14;
    v___x_5102_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(
        v___x_5101_,
        v_codeActionProvider_x3f_5047_,
    );
    v___x_5103_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15;
    v___x_5104_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(
        v___x_5103_,
        v_inlayHintProvider_x3f_5048_,
    );
    crate::leanh::lean_dec(v_inlayHintProvider_x3f_5048_);
    v___x_5105_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16;
    v___x_5106_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(
        v___x_5105_,
        v_signatureHelpProvider_x3f_5049_,
    );
    v___x_5107_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17;
    v___x_5108_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(
        v___x_5107_,
        v_colorProvider_x3f_5050_,
    );
    crate::leanh::lean_dec(v_colorProvider_x3f_5050_);
    v___x_5109_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18;
    v___x_5110_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(
        v___x_5109_,
        v_experimental_x3f_5051_,
    );
    v___x_5111_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5111_, 0, v___x_5110_);
    crate::leanh::lean_ctor_set(v___x_5111_, 1, v___x_5059_);
    v___x_5112_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5112_, 0, v___x_5108_);
    crate::leanh::lean_ctor_set(v___x_5112_, 1, v___x_5111_);
    v___x_5113_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5113_, 0, v___x_5106_);
    crate::leanh::lean_ctor_set(v___x_5113_, 1, v___x_5112_);
    v___x_5114_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5114_, 0, v___x_5104_);
    crate::leanh::lean_ctor_set(v___x_5114_, 1, v___x_5113_);
    v___x_5115_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5115_, 0, v___x_5102_);
    crate::leanh::lean_ctor_set(v___x_5115_, 1, v___x_5114_);
    v___x_5116_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5116_, 0, v___x_5100_);
    crate::leanh::lean_ctor_set(v___x_5116_, 1, v___x_5115_);
    v___x_5117_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5117_, 0, v___x_5098_);
    crate::leanh::lean_ctor_set(v___x_5117_, 1, v___x_5116_);
    v___x_5118_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5118_, 0, v___x_5094_);
    crate::leanh::lean_ctor_set(v___x_5118_, 1, v___x_5117_);
    v___x_5119_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5119_, 0, v___x_5090_);
    crate::leanh::lean_ctor_set(v___x_5119_, 1, v___x_5118_);
    v___x_5120_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5120_, 0, v___x_5088_);
    crate::leanh::lean_ctor_set(v___x_5120_, 1, v___x_5119_);
    v___x_5121_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5121_, 0, v___x_5084_);
    crate::leanh::lean_ctor_set(v___x_5121_, 1, v___x_5120_);
    v___x_5122_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5122_, 0, v___x_5080_);
    crate::leanh::lean_ctor_set(v___x_5122_, 1, v___x_5121_);
    v___x_5123_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5123_, 0, v___x_5076_);
    crate::leanh::lean_ctor_set(v___x_5123_, 1, v___x_5122_);
    v___x_5124_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5124_, 0, v___x_5072_);
    crate::leanh::lean_ctor_set(v___x_5124_, 1, v___x_5123_);
    v___x_5125_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5125_, 0, v___x_5068_);
    crate::leanh::lean_ctor_set(v___x_5125_, 1, v___x_5124_);
    v___x_5126_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5126_, 0, v___x_5064_);
    crate::leanh::lean_ctor_set(v___x_5126_, 1, v___x_5125_);
    v___x_5127_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5127_, 0, v___x_5060_);
    crate::leanh::lean_ctor_set(v___x_5127_, 1, v___x_5126_);
    v___x_5128_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5128_, 0, v___x_5055_);
    crate::leanh::lean_ctor_set(v___x_5128_, 1, v___x_5127_);
    v___x_5129_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5129_, 0, v___x_5053_);
    crate::leanh::lean_ctor_set(v___x_5129_, 1, v___x_5128_);
    v___x_5130_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1;
    v___x_5131_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_5129_, v___x_5130_);
    v___x_5132_ = l_Lean_Json_mkObj(v___x_5131_);
    crate::leanh::lean_dec(v___x_5131_);
    return v___x_5132_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(
    mut v_x_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v_a_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5151_: u8 = 0;
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5137_) == 0 {
                    v___x_5138_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0;
                    return v___x_5138_;
                } else {
                    v___x_5139_ = l_Lean_Lsp_instFromJsonInlayHintOptions_fromJson(v_x_5137_);
                    if crate::leanh::lean_obj_tag(v___x_5139_) == 0 {
                        v_a_5140_ = crate::leanh::lean_ctor_get(v___x_5139_, 0);
                        v_isSharedCheck_5147_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5139_)) as u8;
                        if v_isSharedCheck_5147_ == 0 {
                            v___x_5142_ = v___x_5139_;
                            v_isShared_5143_ = v_isSharedCheck_5147_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5140_);
                            crate::leanh::lean_dec(v___x_5139_);
                            v___x_5142_ = crate::leanh::lean_box(0);
                            v_isShared_5143_ = v_isSharedCheck_5147_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5148_ = crate::leanh::lean_ctor_get(v___x_5139_, 0);
                        v_isSharedCheck_5156_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5139_)) as u8;
                        if v_isSharedCheck_5156_ == 0 {
                            v___x_5150_ = v___x_5139_;
                            v_isShared_5151_ = v_isSharedCheck_5156_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5148_);
                            crate::leanh::lean_dec(v___x_5139_);
                            v___x_5150_ = crate::leanh::lean_box(0);
                            v_isShared_5151_ = v_isSharedCheck_5156_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5143_ == 0 {
                    v___x_5145_ = v___x_5142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
                    v___x_5145_ = v_reuseFailAlloc_5146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5145_;
            }
            3 => {
                v___x_5152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5152_, 0, v_a_5148_);
                if v_isShared_5151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5152_);
                    v___x_5154_ = v___x_5150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(
    mut v_j_5157_: *mut crate::leanh::LeanObject,
    mut v_k_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5159_ = l_Lean_Json_getObjValD(v_j_5157_, v_k_5158_);
    v___x_5160_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(v___x_5159_);
    return v___x_5160_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5___boxed(
    mut v_j_5161_: *mut crate::leanh::LeanObject,
    mut v_k_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5163_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_j_5161_, v_k_5162_);
    crate::leanh::lean_dec_ref(v_k_5162_);
    return v_res_5163_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(
    mut v_x_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5172_: u8 = 0;
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5166_) == 0 {
                    v___x_5167_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0;
                    return v___x_5167_;
                } else {
                    v___x_5168_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson(v_x_5166_);
                    if crate::leanh::lean_obj_tag(v___x_5168_) == 0 {
                        v_a_5169_ = crate::leanh::lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5176_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5176_ == 0 {
                            v___x_5171_ = v___x_5168_;
                            v_isShared_5172_ = v_isSharedCheck_5176_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5169_);
                            crate::leanh::lean_dec(v___x_5168_);
                            v___x_5171_ = crate::leanh::lean_box(0);
                            v_isShared_5172_ = v_isSharedCheck_5176_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5177_ = crate::leanh::lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5179_ = v___x_5168_;
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5177_);
                            crate::leanh::lean_dec(v___x_5168_);
                            v___x_5179_ = crate::leanh::lean_box(0);
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5172_ == 0 {
                    v___x_5174_ = v___x_5171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
                    v___x_5174_ = v_reuseFailAlloc_5175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5174_;
            }
            3 => {
                v___x_5181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5181_, 0, v_a_5177_);
                if v_isShared_5180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5179_, 0, v___x_5181_);
                    v___x_5183_ = v___x_5179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
                    v___x_5183_ = v_reuseFailAlloc_5184_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(
    mut v_j_5186_: *mut crate::leanh::LeanObject,
    mut v_k_5187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = l_Lean_Json_getObjValD(v_j_5186_, v_k_5187_);
    v___x_5189_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4___boxed(
    mut v_j_5190_: *mut crate::leanh::LeanObject,
    mut v_k_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_j_5190_, v_k_5191_);
    crate::leanh::lean_dec_ref(v_k_5191_);
    return v_res_5192_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(
    mut v_x_5195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v_a_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5195_) == 0 {
                    v___x_5196_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0;
                    return v___x_5196_;
                } else {
                    v___x_5197_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(v_x_5195_);
                    if crate::leanh::lean_obj_tag(v___x_5197_) == 0 {
                        v_a_5198_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5205_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5205_ == 0 {
                            v___x_5200_ = v___x_5197_;
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5198_);
                            crate::leanh::lean_dec(v___x_5197_);
                            v___x_5200_ = crate::leanh::lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5206_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5214_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5214_ == 0 {
                            v___x_5208_ = v___x_5197_;
                            v_isShared_5209_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5206_);
                            crate::leanh::lean_dec(v___x_5197_);
                            v___x_5208_ = crate::leanh::lean_box(0);
                            v_isShared_5209_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5201_ == 0 {
                    v___x_5203_ = v___x_5200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5203_;
            }
            3 => {
                v___x_5210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5210_, 0, v_a_5206_);
                if v_isShared_5209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5208_, 0, v___x_5210_);
                    v___x_5212_ = v___x_5208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
                    v___x_5212_ = v_reuseFailAlloc_5213_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(
    mut v_j_5215_: *mut crate::leanh::LeanObject,
    mut v_k_5216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5217_ = l_Lean_Json_getObjValD(v_j_5215_, v_k_5216_);
    v___x_5218_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(v___x_5217_);
    return v___x_5218_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8___boxed(
    mut v_j_5219_: *mut crate::leanh::LeanObject,
    mut v_k_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_j_5219_, v_k_5220_);
    crate::leanh::lean_dec_ref(v_k_5220_);
    return v_res_5221_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(
    mut v_x_5224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5224_) == 0 {
                    v___x_5225_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0;
                    return v___x_5225_;
                } else {
                    v___x_5226_ = l_Lean_Lsp_instFromJsonSignatureHelpOptions_fromJson(v_x_5224_);
                    if crate::leanh::lean_obj_tag(v___x_5226_) == 0 {
                        v_a_5227_ = crate::leanh::lean_ctor_get(v___x_5226_, 0);
                        v_isSharedCheck_5234_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5226_)) as u8;
                        if v_isSharedCheck_5234_ == 0 {
                            v___x_5229_ = v___x_5226_;
                            v_isShared_5230_ = v_isSharedCheck_5234_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5227_);
                            crate::leanh::lean_dec(v___x_5226_);
                            v___x_5229_ = crate::leanh::lean_box(0);
                            v_isShared_5230_ = v_isSharedCheck_5234_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5226_, 0);
                        v_isSharedCheck_5243_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5226_)) as u8;
                        if v_isSharedCheck_5243_ == 0 {
                            v___x_5237_ = v___x_5226_;
                            v_isShared_5238_ = v_isSharedCheck_5243_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5235_);
                            crate::leanh::lean_dec(v___x_5226_);
                            v___x_5237_ = crate::leanh::lean_box(0);
                            v_isShared_5238_ = v_isSharedCheck_5243_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5230_ == 0 {
                    v___x_5232_ = v___x_5229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
                    v___x_5232_ = v_reuseFailAlloc_5233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5232_;
            }
            3 => {
                v___x_5239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5239_, 0, v_a_5235_);
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5239_);
                    v___x_5241_ = v___x_5237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
                    v___x_5241_ = v_reuseFailAlloc_5242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(
    mut v_j_5244_: *mut crate::leanh::LeanObject,
    mut v_k_5245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5246_ = l_Lean_Json_getObjValD(v_j_5244_, v_k_5245_);
    v___x_5247_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(v___x_5246_);
    return v___x_5247_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6___boxed(
    mut v_j_5248_: *mut crate::leanh::LeanObject,
    mut v_k_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_j_5248_, v_k_5249_);
    crate::leanh::lean_dec_ref(v_k_5249_);
    return v_res_5250_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(
    mut v_x_5253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut v_a_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5267_: u8 = 0;
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5253_) == 0 {
                    v___x_5254_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_5254_;
                } else {
                    v___x_5255_ =
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(v_x_5253_);
                    if crate::leanh::lean_obj_tag(v___x_5255_) == 0 {
                        v_a_5256_ = crate::leanh::lean_ctor_get(v___x_5255_, 0);
                        v_isSharedCheck_5263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5255_)) as u8;
                        if v_isSharedCheck_5263_ == 0 {
                            v___x_5258_ = v___x_5255_;
                            v_isShared_5259_ = v_isSharedCheck_5263_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5256_);
                            crate::leanh::lean_dec(v___x_5255_);
                            v___x_5258_ = crate::leanh::lean_box(0);
                            v_isShared_5259_ = v_isSharedCheck_5263_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5264_ = crate::leanh::lean_ctor_get(v___x_5255_, 0);
                        v_isSharedCheck_5272_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5255_)) as u8;
                        if v_isSharedCheck_5272_ == 0 {
                            v___x_5266_ = v___x_5255_;
                            v_isShared_5267_ = v_isSharedCheck_5272_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5264_);
                            crate::leanh::lean_dec(v___x_5255_);
                            v___x_5266_ = crate::leanh::lean_box(0);
                            v_isShared_5267_ = v_isSharedCheck_5272_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5259_ == 0 {
                    v___x_5261_ = v___x_5258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5261_;
            }
            3 => {
                v___x_5268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5268_, 0, v_a_5264_);
                if v_isShared_5267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5266_, 0, v___x_5268_);
                    v___x_5270_ = v___x_5266_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5268_);
                    v___x_5270_ = v_reuseFailAlloc_5271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(
    mut v_j_5273_: *mut crate::leanh::LeanObject,
    mut v_k_5274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5275_ = l_Lean_Json_getObjValD(v_j_5273_, v_k_5274_);
    v___x_5276_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(v___x_5275_);
    return v___x_5276_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0___boxed(
    mut v_j_5277_: *mut crate::leanh::LeanObject,
    mut v_k_5278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5279_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_j_5277_, v_k_5278_);
    crate::leanh::lean_dec_ref(v_k_5278_);
    return v_res_5279_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(
    mut v_x_5282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5288_: u8 = 0;
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5292_: u8 = 0;
    let mut v_a_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5296_: u8 = 0;
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5282_) == 0 {
                    v___x_5283_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0;
                    return v___x_5283_;
                } else {
                    v___x_5284_ = l_Lean_Lsp_instFromJsonCompletionOptions_fromJson(v_x_5282_);
                    if crate::leanh::lean_obj_tag(v___x_5284_) == 0 {
                        v_a_5285_ = crate::leanh::lean_ctor_get(v___x_5284_, 0);
                        v_isSharedCheck_5292_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5284_)) as u8;
                        if v_isSharedCheck_5292_ == 0 {
                            v___x_5287_ = v___x_5284_;
                            v_isShared_5288_ = v_isSharedCheck_5292_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5285_);
                            crate::leanh::lean_dec(v___x_5284_);
                            v___x_5287_ = crate::leanh::lean_box(0);
                            v_isShared_5288_ = v_isSharedCheck_5292_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5293_ = crate::leanh::lean_ctor_get(v___x_5284_, 0);
                        v_isSharedCheck_5301_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5284_)) as u8;
                        if v_isSharedCheck_5301_ == 0 {
                            v___x_5295_ = v___x_5284_;
                            v_isShared_5296_ = v_isSharedCheck_5301_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5293_);
                            crate::leanh::lean_dec(v___x_5284_);
                            v___x_5295_ = crate::leanh::lean_box(0);
                            v_isShared_5296_ = v_isSharedCheck_5301_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5288_ == 0 {
                    v___x_5290_ = v___x_5287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
                    v___x_5290_ = v_reuseFailAlloc_5291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5290_;
            }
            3 => {
                v___x_5297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5297_, 0, v_a_5293_);
                if v_isShared_5296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5295_, 0, v___x_5297_);
                    v___x_5299_ = v___x_5295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
                    v___x_5299_ = v_reuseFailAlloc_5300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(
    mut v_j_5302_: *mut crate::leanh::LeanObject,
    mut v_k_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5304_ = l_Lean_Json_getObjValD(v_j_5302_, v_k_5303_);
    v___x_5305_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(v___x_5304_);
    return v___x_5305_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1___boxed(
    mut v_j_5306_: *mut crate::leanh::LeanObject,
    mut v_k_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5308_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_j_5306_, v_k_5307_);
    crate::leanh::lean_dec_ref(v_k_5307_);
    return v_res_5308_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(
    mut v_x_5309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5319_: u8 = 0;
    let mut v_a_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5323_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5309_) == 0 {
                    v___x_5310_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_5310_;
                } else {
                    v___x_5311_ = l_Lean_Lsp_instFromJsonDocumentColorOptions_fromJson(v_x_5309_);
                    if crate::leanh::lean_obj_tag(v___x_5311_) == 0 {
                        v_a_5312_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5319_ == 0 {
                            v___x_5314_ = v___x_5311_;
                            v_isShared_5315_ = v_isSharedCheck_5319_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5312_);
                            crate::leanh::lean_dec(v___x_5311_);
                            v___x_5314_ = crate::leanh::lean_box(0);
                            v_isShared_5315_ = v_isSharedCheck_5319_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5320_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5328_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5328_ == 0 {
                            v___x_5322_ = v___x_5311_;
                            v_isShared_5323_ = v_isSharedCheck_5328_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5320_);
                            crate::leanh::lean_dec(v___x_5311_);
                            v___x_5322_ = crate::leanh::lean_box(0);
                            v_isShared_5323_ = v_isSharedCheck_5328_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5315_ == 0 {
                    v___x_5317_ = v___x_5314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
                    v___x_5317_ = v_reuseFailAlloc_5318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5317_;
            }
            3 => {
                v___x_5324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5324_, 0, v_a_5320_);
                if v_isShared_5323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5322_, 0, v___x_5324_);
                    v___x_5326_ = v___x_5322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
                    v___x_5326_ = v_reuseFailAlloc_5327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(
    mut v_j_5329_: *mut crate::leanh::LeanObject,
    mut v_k_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5331_ = l_Lean_Json_getObjValD(v_j_5329_, v_k_5330_);
    v___x_5332_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(v___x_5331_);
    return v___x_5332_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7___boxed(
    mut v_j_5333_: *mut crate::leanh::LeanObject,
    mut v_k_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5335_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_j_5333_, v_k_5334_);
    crate::leanh::lean_dec_ref(v_k_5334_);
    return v_res_5335_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(
    mut v_x_5338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5348_: u8 = 0;
    let mut v_a_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5338_) == 0 {
                    v___x_5339_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0;
                    return v___x_5339_;
                } else {
                    v___x_5340_ = l_Lean_Lsp_instFromJsonSemanticTokensOptions_fromJson(v_x_5338_);
                    if crate::leanh::lean_obj_tag(v___x_5340_) == 0 {
                        v_a_5341_ = crate::leanh::lean_ctor_get(v___x_5340_, 0);
                        v_isSharedCheck_5348_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5340_)) as u8;
                        if v_isSharedCheck_5348_ == 0 {
                            v___x_5343_ = v___x_5340_;
                            v_isShared_5344_ = v_isSharedCheck_5348_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5341_);
                            crate::leanh::lean_dec(v___x_5340_);
                            v___x_5343_ = crate::leanh::lean_box(0);
                            v_isShared_5344_ = v_isSharedCheck_5348_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5349_ = crate::leanh::lean_ctor_get(v___x_5340_, 0);
                        v_isSharedCheck_5357_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5340_)) as u8;
                        if v_isSharedCheck_5357_ == 0 {
                            v___x_5351_ = v___x_5340_;
                            v_isShared_5352_ = v_isSharedCheck_5357_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5349_);
                            crate::leanh::lean_dec(v___x_5340_);
                            v___x_5351_ = crate::leanh::lean_box(0);
                            v_isShared_5352_ = v_isSharedCheck_5357_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5344_ == 0 {
                    v___x_5346_ = v___x_5343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
                    v___x_5346_ = v_reuseFailAlloc_5347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5346_;
            }
            3 => {
                v___x_5353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5353_, 0, v_a_5349_);
                if v_isShared_5352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5351_, 0, v___x_5353_);
                    v___x_5355_ = v___x_5351_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(
    mut v_j_5358_: *mut crate::leanh::LeanObject,
    mut v_k_5359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lean_Json_getObjValD(v_j_5358_, v_k_5359_);
    v___x_5361_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(v___x_5360_);
    return v___x_5361_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3___boxed(
    mut v_j_5362_: *mut crate::leanh::LeanObject,
    mut v_k_5363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5364_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_j_5362_, v_k_5363_);
    crate::leanh::lean_dec_ref(v_k_5363_);
    return v_res_5364_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(
    mut v_x_5365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5379_: u8 = 0;
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5365_) == 0 {
                    v___x_5366_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0;
                    return v___x_5366_;
                } else {
                    v___x_5367_ = l_Lean_Lsp_instFromJsonRenameOptions_fromJson(v_x_5365_);
                    if crate::leanh::lean_obj_tag(v___x_5367_) == 0 {
                        v_a_5368_ = crate::leanh::lean_ctor_get(v___x_5367_, 0);
                        v_isSharedCheck_5375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5367_)) as u8;
                        if v_isSharedCheck_5375_ == 0 {
                            v___x_5370_ = v___x_5367_;
                            v_isShared_5371_ = v_isSharedCheck_5375_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5368_);
                            crate::leanh::lean_dec(v___x_5367_);
                            v___x_5370_ = crate::leanh::lean_box(0);
                            v_isShared_5371_ = v_isSharedCheck_5375_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5376_ = crate::leanh::lean_ctor_get(v___x_5367_, 0);
                        v_isSharedCheck_5384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5367_)) as u8;
                        if v_isSharedCheck_5384_ == 0 {
                            v___x_5378_ = v___x_5367_;
                            v_isShared_5379_ = v_isSharedCheck_5384_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5376_);
                            crate::leanh::lean_dec(v___x_5367_);
                            v___x_5378_ = crate::leanh::lean_box(0);
                            v_isShared_5379_ = v_isSharedCheck_5384_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5371_ == 0 {
                    v___x_5373_ = v___x_5370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
                    v___x_5373_ = v_reuseFailAlloc_5374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5373_;
            }
            3 => {
                v___x_5380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5380_, 0, v_a_5376_);
                if v_isShared_5379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5378_, 0, v___x_5380_);
                    v___x_5382_ = v___x_5378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
                    v___x_5382_ = v_reuseFailAlloc_5383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(
    mut v_j_5385_: *mut crate::leanh::LeanObject,
    mut v_k_5386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5387_ = l_Lean_Json_getObjValD(v_j_5385_, v_k_5386_);
    v___x_5388_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(v___x_5387_);
    return v___x_5388_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2___boxed(
    mut v_j_5389_: *mut crate::leanh::LeanObject,
    mut v_k_5390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5391_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_j_5389_, v_k_5390_);
    crate::leanh::lean_dec_ref(v_k_5390_);
    return v_res_5391_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5397_: u8 = 0;
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5397_ = 1;
    v___x_5398_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1;
    v___x_5399_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5398_, v___x_5397_);
    return v___x_5399_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5400_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5;
    v___x_5401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2,
    );
    v___x_5402_ = lean_string_append(v___x_5401_, v___x_5400_);
    return v___x_5402_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5406_: u8 = 0;
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5406_ = 1;
    v___x_5407_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5;
    v___x_5408_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5407_, v___x_5406_);
    return v___x_5408_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6,
    );
    v___x_5410_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5411_ = lean_string_append(v___x_5410_, v___x_5409_);
    return v___x_5411_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5412_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7,
    );
    v___x_5414_ = lean_string_append(v___x_5413_, v___x_5412_);
    return v___x_5414_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5418_: u8 = 0;
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5418_ = 1;
    v___x_5419_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10;
    v___x_5420_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5419_, v___x_5418_);
    return v___x_5420_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5421_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11,
    );
    v___x_5422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5423_ = lean_string_append(v___x_5422_, v___x_5421_);
    return v___x_5423_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5424_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5425_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12,
    );
    v___x_5426_ = lean_string_append(v___x_5425_, v___x_5424_);
    return v___x_5426_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5429_: u8 = 0;
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5429_ = 1;
    v___x_5430_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14;
    v___x_5431_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5430_, v___x_5429_);
    return v___x_5431_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15,
    );
    v___x_5433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5434_ = lean_string_append(v___x_5433_, v___x_5432_);
    return v___x_5434_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5435_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5436_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16,
    );
    v___x_5437_ = lean_string_append(v___x_5436_, v___x_5435_);
    return v___x_5437_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5440_ = 1;
    v___x_5441_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18;
    v___x_5442_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5441_, v___x_5440_);
    return v___x_5442_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19,
    );
    v___x_5444_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5445_ = lean_string_append(v___x_5444_, v___x_5443_);
    return v___x_5445_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5446_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20,
    );
    v___x_5448_ = lean_string_append(v___x_5447_, v___x_5446_);
    return v___x_5448_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5451_: u8 = 0;
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5451_ = 1;
    v___x_5452_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22;
    v___x_5453_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5452_, v___x_5451_);
    return v___x_5453_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5454_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23,
    );
    v___x_5455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5456_ = lean_string_append(v___x_5455_, v___x_5454_);
    return v___x_5456_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5457_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5458_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24,
    );
    v___x_5459_ = lean_string_append(v___x_5458_, v___x_5457_);
    return v___x_5459_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5462_: u8 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5462_ = 1;
    v___x_5463_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26;
    v___x_5464_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5463_, v___x_5462_);
    return v___x_5464_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27,
    );
    v___x_5466_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5467_ = lean_string_append(v___x_5466_, v___x_5465_);
    return v___x_5467_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5468_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5469_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28,
    );
    v___x_5470_ = lean_string_append(v___x_5469_, v___x_5468_);
    return v___x_5470_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5473_: u8 = 0;
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5473_ = 1;
    v___x_5474_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30;
    v___x_5475_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5474_, v___x_5473_);
    return v___x_5475_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5476_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31,
    );
    v___x_5477_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5478_ = lean_string_append(v___x_5477_, v___x_5476_);
    return v___x_5478_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5479_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32,
    );
    v___x_5481_ = lean_string_append(v___x_5480_, v___x_5479_);
    return v___x_5481_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5484_: u8 = 0;
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5484_ = 1;
    v___x_5485_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34;
    v___x_5486_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5485_, v___x_5484_);
    return v___x_5486_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5487_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35,
    );
    v___x_5488_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5489_ = lean_string_append(v___x_5488_, v___x_5487_);
    return v___x_5489_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5491_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36,
    );
    v___x_5492_ = lean_string_append(v___x_5491_, v___x_5490_);
    return v___x_5492_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5495_: u8 = 0;
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5495_ = 1;
    v___x_5496_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38;
    v___x_5497_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5496_, v___x_5495_);
    return v___x_5497_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5498_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39,
    );
    v___x_5499_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5500_ = lean_string_append(v___x_5499_, v___x_5498_);
    return v___x_5500_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5501_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5502_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40,
    );
    v___x_5503_ = lean_string_append(v___x_5502_, v___x_5501_);
    return v___x_5503_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5506_: u8 = 0;
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5506_ = 1;
    v___x_5507_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42;
    v___x_5508_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5507_, v___x_5506_);
    return v___x_5508_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43,
    );
    v___x_5510_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5511_ = lean_string_append(v___x_5510_, v___x_5509_);
    return v___x_5511_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5512_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5513_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44,
    );
    v___x_5514_ = lean_string_append(v___x_5513_, v___x_5512_);
    return v___x_5514_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5518_: u8 = 0;
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5518_ = 1;
    v___x_5519_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47;
    v___x_5520_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5519_, v___x_5518_);
    return v___x_5520_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5521_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48,
    );
    v___x_5522_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5523_ = lean_string_append(v___x_5522_, v___x_5521_);
    return v___x_5523_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5524_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5525_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49,
    );
    v___x_5526_ = lean_string_append(v___x_5525_, v___x_5524_);
    return v___x_5526_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5529_: u8 = 0;
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5529_ = 1;
    v___x_5530_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51;
    v___x_5531_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5530_, v___x_5529_);
    return v___x_5531_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52,
    );
    v___x_5533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5534_ = lean_string_append(v___x_5533_, v___x_5532_);
    return v___x_5534_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5535_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53,
    );
    v___x_5537_ = lean_string_append(v___x_5536_, v___x_5535_);
    return v___x_5537_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5540_: u8 = 0;
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5540_ = 1;
    v___x_5541_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55;
    v___x_5542_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5541_, v___x_5540_);
    return v___x_5542_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56,
    );
    v___x_5544_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5545_ = lean_string_append(v___x_5544_, v___x_5543_);
    return v___x_5545_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5546_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5547_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57,
    );
    v___x_5548_ = lean_string_append(v___x_5547_, v___x_5546_);
    return v___x_5548_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5552_: u8 = 0;
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5552_ = 1;
    v___x_5553_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60;
    v___x_5554_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5553_, v___x_5552_);
    return v___x_5554_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5555_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61,
    );
    v___x_5556_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5557_ = lean_string_append(v___x_5556_, v___x_5555_);
    return v___x_5557_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5558_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5559_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62,
    );
    v___x_5560_ = lean_string_append(v___x_5559_, v___x_5558_);
    return v___x_5560_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5564_: u8 = 0;
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5564_ = 1;
    v___x_5565_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65;
    v___x_5566_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5565_, v___x_5564_);
    return v___x_5566_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5567_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66,
    );
    v___x_5568_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5569_ = lean_string_append(v___x_5568_, v___x_5567_);
    return v___x_5569_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5570_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67,
    );
    v___x_5572_ = lean_string_append(v___x_5571_, v___x_5570_);
    return v___x_5572_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5576_: u8 = 0;
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5576_ = 1;
    v___x_5577_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70;
    v___x_5578_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5577_, v___x_5576_);
    return v___x_5578_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5579_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71,
    );
    v___x_5580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5581_ = lean_string_append(v___x_5580_, v___x_5579_);
    return v___x_5581_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5582_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72,
    );
    v___x_5584_ = lean_string_append(v___x_5583_, v___x_5582_);
    return v___x_5584_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5588_: u8 = 0;
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5588_ = 1;
    v___x_5589_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75;
    v___x_5590_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5589_, v___x_5588_);
    return v___x_5590_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5591_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76,
    );
    v___x_5592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5593_ = lean_string_append(v___x_5592_, v___x_5591_);
    return v___x_5593_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5594_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5595_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77,
    );
    v___x_5596_ = lean_string_append(v___x_5595_, v___x_5594_);
    return v___x_5596_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5600_ = 1;
    v___x_5601_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80;
    v___x_5602_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5601_, v___x_5600_);
    return v___x_5602_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81,
    );
    v___x_5604_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5605_ = lean_string_append(v___x_5604_, v___x_5603_);
    return v___x_5605_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5606_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5607_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82,
    );
    v___x_5608_ = lean_string_append(v___x_5607_, v___x_5606_);
    return v___x_5608_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5612_ = 1;
    v___x_5613_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85;
    v___x_5614_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5613_, v___x_5612_);
    return v___x_5614_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5615_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86,
    );
    v___x_5616_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3,
    );
    v___x_5617_ = lean_string_append(v___x_5616_, v___x_5615_);
    return v___x_5617_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5618_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11;
    v___x_5619_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87_once
        ),
        _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87,
    );
    v___x_5620_ = lean_string_append(v___x_5619_, v___x_5618_);
    return v___x_5620_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(
    mut v_json_5621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5627_: u8 = 0;
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5633_: u8 = 0;
    let mut v_a_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5637_: u8 = 0;
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5641_: u8 = 0;
    let mut v_a_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5648_: u8 = 0;
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5654_: u8 = 0;
    let mut v_a_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5658_: u8 = 0;
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5662_: u8 = 0;
    let mut v_a_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5669_: u8 = 0;
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v_a_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5679_: u8 = 0;
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5683_: u8 = 0;
    let mut v_a_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5690_: u8 = 0;
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5696_: u8 = 0;
    let mut v_a_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5704_: u8 = 0;
    let mut v_a_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5711_: u8 = 0;
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5717_: u8 = 0;
    let mut v_a_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut v_a_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5738_: u8 = 0;
    let mut v_a_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5742_: u8 = 0;
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5746_: u8 = 0;
    let mut v_a_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5753_: u8 = 0;
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5759_: u8 = 0;
    let mut v_a_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5763_: u8 = 0;
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5767_: u8 = 0;
    let mut v_a_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5774_: u8 = 0;
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5780_: u8 = 0;
    let mut v_a_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5784_: u8 = 0;
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5788_: u8 = 0;
    let mut v_a_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5801_: u8 = 0;
    let mut v_a_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5805_: u8 = 0;
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5809_: u8 = 0;
    let mut v_a_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5822_: u8 = 0;
    let mut v_a_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5826_: u8 = 0;
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5830_: u8 = 0;
    let mut v_a_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5837_: u8 = 0;
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_a_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5847_: u8 = 0;
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5851_: u8 = 0;
    let mut v_a_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5858_: u8 = 0;
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5864_: u8 = 0;
    let mut v_a_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5868_: u8 = 0;
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5872_: u8 = 0;
    let mut v_a_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5879_: u8 = 0;
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5885_: u8 = 0;
    let mut v_a_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5889_: u8 = 0;
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5893_: u8 = 0;
    let mut v_a_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5900_: u8 = 0;
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v_a_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5910_: u8 = 0;
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5914_: u8 = 0;
    let mut v_a_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5921_: u8 = 0;
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut v_a_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5942_: u8 = 0;
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5948_: u8 = 0;
    let mut v_a_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5952_: u8 = 0;
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5956_: u8 = 0;
    let mut v_a_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5963_: u8 = 0;
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5969_: u8 = 0;
    let mut v_a_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5973_: u8 = 0;
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5977_: u8 = 0;
    let mut v_a_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut v_a_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5994_: u8 = 0;
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5998_: u8 = 0;
    let mut v_a_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6005_: u8 = 0;
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6011_: u8 = 0;
    let mut v_a_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6015_: u8 = 0;
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6019_: u8 = 0;
    let mut v_a_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6023_: u8 = 0;
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: u8 = 0;
    let mut v___x_6026_: u8 = 0;
    let mut v___x_6027_: u8 = 0;
    let mut v___x_6028_: u8 = 0;
    let mut v___x_6029_: u8 = 0;
    let mut v___x_6030_: u8 = 0;
    let mut v___x_6031_: u8 = 0;
    let mut v___x_6032_: u8 = 0;
    let mut v___x_6033_: u8 = 0;
    let mut v___x_6034_: u8 = 0;
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5622_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0;
                crate::leanh::lean_inc(v_json_5621_);
                v___x_5623_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_json_5621_, v___x_5622_);
                if crate::leanh::lean_obj_tag(v___x_5623_) == 0 {
                    crate::leanh::lean_dec(v_json_5621_);
                    v_a_5624_ = crate::leanh::lean_ctor_get(v___x_5623_, 0);
                    v_isSharedCheck_5633_ = (!crate::leanh::lean_is_exclusive(v___x_5623_)) as u8;
                    if v_isSharedCheck_5633_ == 0 {
                        v___x_5626_ = v___x_5623_;
                        v_isShared_5627_ = v_isSharedCheck_5633_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5624_);
                        crate::leanh::lean_dec(v___x_5623_);
                        v___x_5626_ = crate::leanh::lean_box(0);
                        v_isShared_5627_ = v_isSharedCheck_5633_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_5623_) == 0 {
                        crate::leanh::lean_dec(v_json_5621_);
                        v_a_5634_ = crate::leanh::lean_ctor_get(v___x_5623_, 0);
                        v_isSharedCheck_5641_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5623_)) as u8;
                        if v_isSharedCheck_5641_ == 0 {
                            v___x_5636_ = v___x_5623_;
                            v_isShared_5637_ = v_isSharedCheck_5641_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5634_);
                            crate::leanh::lean_dec(v___x_5623_);
                            v___x_5636_ = crate::leanh::lean_box(0);
                            v_isShared_5637_ = v_isSharedCheck_5641_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5642_ = crate::leanh::lean_ctor_get(v___x_5623_, 0);
                        crate::leanh::lean_inc(v_a_5642_);
                        crate::leanh::lean_dec_ref_known(v___x_5623_, 1);
                        v___x_5643_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_5621_);
                        v___x_5644_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_json_5621_, v___x_5643_);
                        if crate::leanh::lean_obj_tag(v___x_5644_) == 0 {
                            crate::leanh::lean_dec(v_a_5642_);
                            crate::leanh::lean_dec(v_json_5621_);
                            v_a_5645_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                            v_isSharedCheck_5654_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5644_)) as u8;
                            if v_isSharedCheck_5654_ == 0 {
                                v___x_5647_ = v___x_5644_;
                                v_isShared_5648_ = v_isSharedCheck_5654_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5645_);
                                crate::leanh::lean_dec(v___x_5644_);
                                v___x_5647_ = crate::leanh::lean_box(0);
                                v_isShared_5648_ = v_isSharedCheck_5654_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_5644_) == 0 {
                                crate::leanh::lean_dec(v_a_5642_);
                                crate::leanh::lean_dec(v_json_5621_);
                                v_a_5655_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                                v_isSharedCheck_5662_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5644_)) as u8;
                                if v_isSharedCheck_5662_ == 0 {
                                    v___x_5657_ = v___x_5644_;
                                    v_isShared_5658_ = v_isSharedCheck_5662_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5655_);
                                    crate::leanh::lean_dec(v___x_5644_);
                                    v___x_5657_ = crate::leanh::lean_box(0);
                                    v_isShared_5658_ = v_isSharedCheck_5662_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5663_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                                crate::leanh::lean_inc(v_a_5663_);
                                crate::leanh::lean_dec_ref_known(v___x_5644_, 1);
                                v___x_5664_ =
                                    l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2;
                                crate::leanh::lean_inc(v_json_5621_);
                                v___x_5665_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5664_);
                                if crate::leanh::lean_obj_tag(v___x_5665_) == 0 {
                                    crate::leanh::lean_dec(v_a_5663_);
                                    crate::leanh::lean_dec(v_a_5642_);
                                    crate::leanh::lean_dec(v_json_5621_);
                                    v_a_5666_ = crate::leanh::lean_ctor_get(v___x_5665_, 0);
                                    v_isSharedCheck_5675_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5665_)) as u8;
                                    if v_isSharedCheck_5675_ == 0 {
                                        v___x_5668_ = v___x_5665_;
                                        v_isShared_5669_ = v_isSharedCheck_5675_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5666_);
                                        crate::leanh::lean_dec(v___x_5665_);
                                        v___x_5668_ = crate::leanh::lean_box(0);
                                        v_isShared_5669_ = v_isSharedCheck_5675_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_5665_) == 0 {
                                        crate::leanh::lean_dec(v_a_5663_);
                                        crate::leanh::lean_dec(v_a_5642_);
                                        crate::leanh::lean_dec(v_json_5621_);
                                        v_a_5676_ = crate::leanh::lean_ctor_get(v___x_5665_, 0);
                                        v_isSharedCheck_5683_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5665_)) as u8;
                                        if v_isSharedCheck_5683_ == 0 {
                                            v___x_5678_ = v___x_5665_;
                                            v_isShared_5679_ = v_isSharedCheck_5683_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5676_);
                                            crate::leanh::lean_dec(v___x_5665_);
                                            v___x_5678_ = crate::leanh::lean_box(0);
                                            v_isShared_5679_ = v_isSharedCheck_5683_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5684_ = crate::leanh::lean_ctor_get(v___x_5665_, 0);
                                        crate::leanh::lean_inc(v_a_5684_);
                                        crate::leanh::lean_dec_ref_known(v___x_5665_, 1);
                                        v___x_5685_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3;
                                        crate::leanh::lean_inc(v_json_5621_);
                                        v___x_5686_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5685_);
                                        if crate::leanh::lean_obj_tag(v___x_5686_) == 0 {
                                            crate::leanh::lean_dec(v_a_5684_);
                                            crate::leanh::lean_dec(v_a_5663_);
                                            crate::leanh::lean_dec(v_a_5642_);
                                            crate::leanh::lean_dec(v_json_5621_);
                                            v_a_5687_ = crate::leanh::lean_ctor_get(v___x_5686_, 0);
                                            v_isSharedCheck_5696_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5686_))
                                                    as u8;
                                            if v_isSharedCheck_5696_ == 0 {
                                                v___x_5689_ = v___x_5686_;
                                                v_isShared_5690_ = v_isSharedCheck_5696_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5687_);
                                                crate::leanh::lean_dec(v___x_5686_);
                                                v___x_5689_ = crate::leanh::lean_box(0);
                                                v_isShared_5690_ = v_isSharedCheck_5696_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_5686_) == 0 {
                                                crate::leanh::lean_dec(v_a_5684_);
                                                crate::leanh::lean_dec(v_a_5663_);
                                                crate::leanh::lean_dec(v_a_5642_);
                                                crate::leanh::lean_dec(v_json_5621_);
                                                v_a_5697_ =
                                                    crate::leanh::lean_ctor_get(v___x_5686_, 0);
                                                v_isSharedCheck_5704_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5686_))
                                                        as u8;
                                                if v_isSharedCheck_5704_ == 0 {
                                                    v___x_5699_ = v___x_5686_;
                                                    v_isShared_5700_ = v_isSharedCheck_5704_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5697_);
                                                    crate::leanh::lean_dec(v___x_5686_);
                                                    v___x_5699_ = crate::leanh::lean_box(0);
                                                    v_isShared_5700_ = v_isSharedCheck_5704_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5705_ =
                                                    crate::leanh::lean_ctor_get(v___x_5686_, 0);
                                                crate::leanh::lean_inc(v_a_5705_);
                                                crate::leanh::lean_dec_ref_known(v___x_5686_, 1);
                                                v___x_5706_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4;
                                                crate::leanh::lean_inc(v_json_5621_);
                                                v___x_5707_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5706_);
                                                if crate::leanh::lean_obj_tag(v___x_5707_) == 0 {
                                                    crate::leanh::lean_dec(v_a_5705_);
                                                    crate::leanh::lean_dec(v_a_5684_);
                                                    crate::leanh::lean_dec(v_a_5663_);
                                                    crate::leanh::lean_dec(v_a_5642_);
                                                    crate::leanh::lean_dec(v_json_5621_);
                                                    v_a_5708_ =
                                                        crate::leanh::lean_ctor_get(v___x_5707_, 0);
                                                    v_isSharedCheck_5717_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5707_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5717_ == 0 {
                                                        v___x_5710_ = v___x_5707_;
                                                        v_isShared_5711_ = v_isSharedCheck_5717_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5708_);
                                                        crate::leanh::lean_dec(v___x_5707_);
                                                        v___x_5710_ = crate::leanh::lean_box(0);
                                                        v_isShared_5711_ = v_isSharedCheck_5717_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if crate::leanh::lean_obj_tag(v___x_5707_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_5705_);
                                                        crate::leanh::lean_dec(v_a_5684_);
                                                        crate::leanh::lean_dec(v_a_5663_);
                                                        crate::leanh::lean_dec(v_a_5642_);
                                                        crate::leanh::lean_dec(v_json_5621_);
                                                        v_a_5718_ = crate::leanh::lean_ctor_get(
                                                            v___x_5707_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5725_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_5707_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5725_ == 0 {
                                                            v___x_5720_ = v___x_5707_;
                                                            v_isShared_5721_ =
                                                                v_isSharedCheck_5725_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_5718_);
                                                            crate::leanh::lean_dec(v___x_5707_);
                                                            v___x_5720_ = crate::leanh::lean_box(0);
                                                            v_isShared_5721_ =
                                                                v_isSharedCheck_5725_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_5726_ = crate::leanh::lean_ctor_get(
                                                            v___x_5707_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_5726_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_5707_,
                                                            1,
                                                        );
                                                        v___x_5727_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5;
                                                        crate::leanh::lean_inc(v_json_5621_);
                                                        v___x_5728_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5727_);
                                                        if crate::leanh::lean_obj_tag(v___x_5728_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_5726_);
                                                            crate::leanh::lean_dec(v_a_5705_);
                                                            crate::leanh::lean_dec(v_a_5684_);
                                                            crate::leanh::lean_dec(v_a_5663_);
                                                            crate::leanh::lean_dec(v_a_5642_);
                                                            crate::leanh::lean_dec(v_json_5621_);
                                                            v_a_5729_ = crate::leanh::lean_ctor_get(
                                                                v___x_5728_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5738_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_5728_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5738_ == 0 {
                                                                v___x_5731_ = v___x_5728_;
                                                                v_isShared_5732_ =
                                                                    v_isSharedCheck_5738_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_5729_);
                                                                crate::leanh::lean_dec(v___x_5728_);
                                                                v___x_5731_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_5732_ =
                                                                    v_isSharedCheck_5738_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_5728_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec(v_a_5726_);
                                                                crate::leanh::lean_dec(v_a_5705_);
                                                                crate::leanh::lean_dec(v_a_5684_);
                                                                crate::leanh::lean_dec(v_a_5663_);
                                                                crate::leanh::lean_dec(v_a_5642_);
                                                                crate::leanh::lean_dec(
                                                                    v_json_5621_,
                                                                );
                                                                v_a_5739_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5728_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5746_ = (!crate::leanh::lean_is_exclusive(v___x_5728_)) as u8;
                                                                if v_isSharedCheck_5746_ == 0 {
                                                                    v___x_5741_ = v___x_5728_;
                                                                    v_isShared_5742_ =
                                                                        v_isSharedCheck_5746_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_5739_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_5728_,
                                                                    );
                                                                    v___x_5741_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_5742_ =
                                                                        v_isSharedCheck_5746_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_5747_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5728_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_5747_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_5728_,
                                                                    1,
                                                                );
                                                                v___x_5748_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6;
                                                                crate::leanh::lean_inc(
                                                                    v_json_5621_,
                                                                );
                                                                v___x_5749_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5748_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_5749_,
                                                                ) == 0
                                                                {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5747_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5726_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5705_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5684_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5663_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5642_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_json_5621_,
                                                                    );
                                                                    v_a_5750_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_5749_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5759_ = (!crate::leanh::lean_is_exclusive(v___x_5749_)) as u8;
                                                                    if v_isSharedCheck_5759_ == 0 {
                                                                        v___x_5752_ = v___x_5749_;
                                                                        v_isShared_5753_ =
                                                                            v_isSharedCheck_5759_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_5750_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_5749_,
                                                                        );
                                                                        v___x_5752_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5753_ =
                                                                            v_isSharedCheck_5759_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_5749_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5747_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5726_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5705_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5684_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5663_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5642_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_json_5621_,
                                                                        );
                                                                        v_a_5760_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                                                                        v_isSharedCheck_5767_ = (!crate::leanh::lean_is_exclusive(v___x_5749_)) as u8;
                                                                        if v_isSharedCheck_5767_
                                                                            == 0
                                                                        {
                                                                            v___x_5762_ =
                                                                                v___x_5749_;
                                                                            v_isShared_5763_ = v_isSharedCheck_5767_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_5760_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_5749_,
                                                                            );
                                                                            v___x_5762_ = crate::leanh::lean_box(0);
                                                                            v_isShared_5763_ = v_isSharedCheck_5767_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_5768_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_5768_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_5749_, 1);
                                                                        v___x_5769_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7;
                                                                        crate::leanh::lean_inc(
                                                                            v_json_5621_,
                                                                        );
                                                                        v___x_5770_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5769_);
                                                                        if crate::leanh::lean_obj_tag(v___x_5770_) == 0 {
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5771_ = crate::leanh::lean_ctor_get(v___x_5770_, 0);
v_isSharedCheck_5780_ = (!crate::leanh::lean_is_exclusive(v___x_5770_)) as u8;
if v_isSharedCheck_5780_ == 0 {
v___x_5773_ = v___x_5770_;
v_isShared_5774_ = v_isSharedCheck_5780_;
state = 29; continue;
} else {
crate::leanh::lean_inc(v_a_5771_);
crate::leanh::lean_dec(v___x_5770_);
v___x_5773_ = crate::leanh::lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5780_;
state = 29; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5770_) == 0 {
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5781_ = crate::leanh::lean_ctor_get(v___x_5770_, 0);
v_isSharedCheck_5788_ = (!crate::leanh::lean_is_exclusive(v___x_5770_)) as u8;
if v_isSharedCheck_5788_ == 0 {
v___x_5783_ = v___x_5770_;
v_isShared_5784_ = v_isSharedCheck_5788_;
state = 31; continue;
} else {
crate::leanh::lean_inc(v_a_5781_);
crate::leanh::lean_dec(v___x_5770_);
v___x_5783_ = crate::leanh::lean_box(0);
v_isShared_5784_ = v_isSharedCheck_5788_;
state = 31; continue;
}
} else {
v_a_5789_ = crate::leanh::lean_ctor_get(v___x_5770_, 0);
crate::leanh::lean_inc(v_a_5789_);
crate::leanh::lean_dec_ref_known(v___x_5770_, 1);
v___x_5790_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8;
crate::leanh::lean_inc(v_json_5621_);
v___x_5791_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5790_);
if crate::leanh::lean_obj_tag(v___x_5791_) == 0 {
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5792_ = crate::leanh::lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5801_ = (!crate::leanh::lean_is_exclusive(v___x_5791_)) as u8;
if v_isSharedCheck_5801_ == 0 {
v___x_5794_ = v___x_5791_;
v_isShared_5795_ = v_isSharedCheck_5801_;
state = 33; continue;
} else {
crate::leanh::lean_inc(v_a_5792_);
crate::leanh::lean_dec(v___x_5791_);
v___x_5794_ = crate::leanh::lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5801_;
state = 33; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5791_) == 0 {
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5802_ = crate::leanh::lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5809_ = (!crate::leanh::lean_is_exclusive(v___x_5791_)) as u8;
if v_isSharedCheck_5809_ == 0 {
v___x_5804_ = v___x_5791_;
v_isShared_5805_ = v_isSharedCheck_5809_;
state = 35; continue;
} else {
crate::leanh::lean_inc(v_a_5802_);
crate::leanh::lean_dec(v___x_5791_);
v___x_5804_ = crate::leanh::lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5809_;
state = 35; continue;
}
} else {
v_a_5810_ = crate::leanh::lean_ctor_get(v___x_5791_, 0);
crate::leanh::lean_inc(v_a_5810_);
crate::leanh::lean_dec_ref_known(v___x_5791_, 1);
v___x_5811_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9;
crate::leanh::lean_inc(v_json_5621_);
v___x_5812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5811_);
if crate::leanh::lean_obj_tag(v___x_5812_) == 0 {
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5813_ = crate::leanh::lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5822_ = (!crate::leanh::lean_is_exclusive(v___x_5812_)) as u8;
if v_isSharedCheck_5822_ == 0 {
v___x_5815_ = v___x_5812_;
v_isShared_5816_ = v_isSharedCheck_5822_;
state = 37; continue;
} else {
crate::leanh::lean_inc(v_a_5813_);
crate::leanh::lean_dec(v___x_5812_);
v___x_5815_ = crate::leanh::lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5822_;
state = 37; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5812_) == 0 {
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5823_ = crate::leanh::lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5830_ = (!crate::leanh::lean_is_exclusive(v___x_5812_)) as u8;
if v_isSharedCheck_5830_ == 0 {
v___x_5825_ = v___x_5812_;
v_isShared_5826_ = v_isSharedCheck_5830_;
state = 39; continue;
} else {
crate::leanh::lean_inc(v_a_5823_);
crate::leanh::lean_dec(v___x_5812_);
v___x_5825_ = crate::leanh::lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5830_;
state = 39; continue;
}
} else {
v_a_5831_ = crate::leanh::lean_ctor_get(v___x_5812_, 0);
crate::leanh::lean_inc(v_a_5831_);
crate::leanh::lean_dec_ref_known(v___x_5812_, 1);
v___x_5832_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10;
crate::leanh::lean_inc(v_json_5621_);
v___x_5833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_json_5621_, v___x_5832_);
if crate::leanh::lean_obj_tag(v___x_5833_) == 0 {
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5834_ = crate::leanh::lean_ctor_get(v___x_5833_, 0);
v_isSharedCheck_5843_ = (!crate::leanh::lean_is_exclusive(v___x_5833_)) as u8;
if v_isSharedCheck_5843_ == 0 {
v___x_5836_ = v___x_5833_;
v_isShared_5837_ = v_isSharedCheck_5843_;
state = 41; continue;
} else {
crate::leanh::lean_inc(v_a_5834_);
crate::leanh::lean_dec(v___x_5833_);
v___x_5836_ = crate::leanh::lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5843_;
state = 41; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5833_) == 0 {
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5844_ = crate::leanh::lean_ctor_get(v___x_5833_, 0);
v_isSharedCheck_5851_ = (!crate::leanh::lean_is_exclusive(v___x_5833_)) as u8;
if v_isSharedCheck_5851_ == 0 {
v___x_5846_ = v___x_5833_;
v_isShared_5847_ = v_isSharedCheck_5851_;
state = 43; continue;
} else {
crate::leanh::lean_inc(v_a_5844_);
crate::leanh::lean_dec(v___x_5833_);
v___x_5846_ = crate::leanh::lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5851_;
state = 43; continue;
}
} else {
v_a_5852_ = crate::leanh::lean_ctor_get(v___x_5833_, 0);
crate::leanh::lean_inc(v_a_5852_);
crate::leanh::lean_dec_ref_known(v___x_5833_, 1);
v___x_5853_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11;
crate::leanh::lean_inc(v_json_5621_);
v___x_5854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5853_);
if crate::leanh::lean_obj_tag(v___x_5854_) == 0 {
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5855_ = crate::leanh::lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5864_ = (!crate::leanh::lean_is_exclusive(v___x_5854_)) as u8;
if v_isSharedCheck_5864_ == 0 {
v___x_5857_ = v___x_5854_;
v_isShared_5858_ = v_isSharedCheck_5864_;
state = 45; continue;
} else {
crate::leanh::lean_inc(v_a_5855_);
crate::leanh::lean_dec(v___x_5854_);
v___x_5857_ = crate::leanh::lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5864_;
state = 45; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5854_) == 0 {
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5865_ = crate::leanh::lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5872_ = (!crate::leanh::lean_is_exclusive(v___x_5854_)) as u8;
if v_isSharedCheck_5872_ == 0 {
v___x_5867_ = v___x_5854_;
v_isShared_5868_ = v_isSharedCheck_5872_;
state = 47; continue;
} else {
crate::leanh::lean_inc(v_a_5865_);
crate::leanh::lean_dec(v___x_5854_);
v___x_5867_ = crate::leanh::lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5872_;
state = 47; continue;
}
} else {
v_a_5873_ = crate::leanh::lean_ctor_get(v___x_5854_, 0);
crate::leanh::lean_inc(v_a_5873_);
crate::leanh::lean_dec_ref_known(v___x_5854_, 1);
v___x_5874_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12;
crate::leanh::lean_inc(v_json_5621_);
v___x_5875_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_5621_, v___x_5874_);
if crate::leanh::lean_obj_tag(v___x_5875_) == 0 {
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5876_ = crate::leanh::lean_ctor_get(v___x_5875_, 0);
v_isSharedCheck_5885_ = (!crate::leanh::lean_is_exclusive(v___x_5875_)) as u8;
if v_isSharedCheck_5885_ == 0 {
v___x_5878_ = v___x_5875_;
v_isShared_5879_ = v_isSharedCheck_5885_;
state = 49; continue;
} else {
crate::leanh::lean_inc(v_a_5876_);
crate::leanh::lean_dec(v___x_5875_);
v___x_5878_ = crate::leanh::lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5885_;
state = 49; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5875_) == 0 {
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5886_ = crate::leanh::lean_ctor_get(v___x_5875_, 0);
v_isSharedCheck_5893_ = (!crate::leanh::lean_is_exclusive(v___x_5875_)) as u8;
if v_isSharedCheck_5893_ == 0 {
v___x_5888_ = v___x_5875_;
v_isShared_5889_ = v_isSharedCheck_5893_;
state = 51; continue;
} else {
crate::leanh::lean_inc(v_a_5886_);
crate::leanh::lean_dec(v___x_5875_);
v___x_5888_ = crate::leanh::lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5893_;
state = 51; continue;
}
} else {
v_a_5894_ = crate::leanh::lean_ctor_get(v___x_5875_, 0);
crate::leanh::lean_inc(v_a_5894_);
crate::leanh::lean_dec_ref_known(v___x_5875_, 1);
v___x_5895_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13;
crate::leanh::lean_inc(v_json_5621_);
v___x_5896_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_json_5621_, v___x_5895_);
if crate::leanh::lean_obj_tag(v___x_5896_) == 0 {
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5897_ = crate::leanh::lean_ctor_get(v___x_5896_, 0);
v_isSharedCheck_5906_ = (!crate::leanh::lean_is_exclusive(v___x_5896_)) as u8;
if v_isSharedCheck_5906_ == 0 {
v___x_5899_ = v___x_5896_;
v_isShared_5900_ = v_isSharedCheck_5906_;
state = 53; continue;
} else {
crate::leanh::lean_inc(v_a_5897_);
crate::leanh::lean_dec(v___x_5896_);
v___x_5899_ = crate::leanh::lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5906_;
state = 53; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5896_) == 0 {
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5907_ = crate::leanh::lean_ctor_get(v___x_5896_, 0);
v_isSharedCheck_5914_ = (!crate::leanh::lean_is_exclusive(v___x_5896_)) as u8;
if v_isSharedCheck_5914_ == 0 {
v___x_5909_ = v___x_5896_;
v_isShared_5910_ = v_isSharedCheck_5914_;
state = 55; continue;
} else {
crate::leanh::lean_inc(v_a_5907_);
crate::leanh::lean_dec(v___x_5896_);
v___x_5909_ = crate::leanh::lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5914_;
state = 55; continue;
}
} else {
v_a_5915_ = crate::leanh::lean_ctor_get(v___x_5896_, 0);
crate::leanh::lean_inc(v_a_5915_);
crate::leanh::lean_dec_ref_known(v___x_5896_, 1);
v___x_5916_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14;
crate::leanh::lean_inc(v_json_5621_);
v___x_5917_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_json_5621_, v___x_5916_);
if crate::leanh::lean_obj_tag(v___x_5917_) == 0 {
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5918_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
v_isSharedCheck_5927_ = (!crate::leanh::lean_is_exclusive(v___x_5917_)) as u8;
if v_isSharedCheck_5927_ == 0 {
v___x_5920_ = v___x_5917_;
v_isShared_5921_ = v_isSharedCheck_5927_;
state = 57; continue;
} else {
crate::leanh::lean_inc(v_a_5918_);
crate::leanh::lean_dec(v___x_5917_);
v___x_5920_ = crate::leanh::lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5927_;
state = 57; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5917_) == 0 {
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5928_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
v_isSharedCheck_5935_ = (!crate::leanh::lean_is_exclusive(v___x_5917_)) as u8;
if v_isSharedCheck_5935_ == 0 {
v___x_5930_ = v___x_5917_;
v_isShared_5931_ = v_isSharedCheck_5935_;
state = 59; continue;
} else {
crate::leanh::lean_inc(v_a_5928_);
crate::leanh::lean_dec(v___x_5917_);
v___x_5930_ = crate::leanh::lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5935_;
state = 59; continue;
}
} else {
v_a_5936_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
crate::leanh::lean_inc(v_a_5936_);
crate::leanh::lean_dec_ref_known(v___x_5917_, 1);
v___x_5937_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15;
crate::leanh::lean_inc(v_json_5621_);
v___x_5938_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_json_5621_, v___x_5937_);
if crate::leanh::lean_obj_tag(v___x_5938_) == 0 {
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5939_ = crate::leanh::lean_ctor_get(v___x_5938_, 0);
v_isSharedCheck_5948_ = (!crate::leanh::lean_is_exclusive(v___x_5938_)) as u8;
if v_isSharedCheck_5948_ == 0 {
v___x_5941_ = v___x_5938_;
v_isShared_5942_ = v_isSharedCheck_5948_;
state = 61; continue;
} else {
crate::leanh::lean_inc(v_a_5939_);
crate::leanh::lean_dec(v___x_5938_);
v___x_5941_ = crate::leanh::lean_box(0);
v_isShared_5942_ = v_isSharedCheck_5948_;
state = 61; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5938_) == 0 {
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5949_ = crate::leanh::lean_ctor_get(v___x_5938_, 0);
v_isSharedCheck_5956_ = (!crate::leanh::lean_is_exclusive(v___x_5938_)) as u8;
if v_isSharedCheck_5956_ == 0 {
v___x_5951_ = v___x_5938_;
v_isShared_5952_ = v_isSharedCheck_5956_;
state = 63; continue;
} else {
crate::leanh::lean_inc(v_a_5949_);
crate::leanh::lean_dec(v___x_5938_);
v___x_5951_ = crate::leanh::lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5956_;
state = 63; continue;
}
} else {
v_a_5957_ = crate::leanh::lean_ctor_get(v___x_5938_, 0);
crate::leanh::lean_inc(v_a_5957_);
crate::leanh::lean_dec_ref_known(v___x_5938_, 1);
v___x_5958_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16;
crate::leanh::lean_inc(v_json_5621_);
v___x_5959_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_json_5621_, v___x_5958_);
if crate::leanh::lean_obj_tag(v___x_5959_) == 0 {
crate::leanh::lean_dec(v_a_5957_);
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5960_ = crate::leanh::lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_5969_ = (!crate::leanh::lean_is_exclusive(v___x_5959_)) as u8;
if v_isSharedCheck_5969_ == 0 {
v___x_5962_ = v___x_5959_;
v_isShared_5963_ = v_isSharedCheck_5969_;
state = 65; continue;
} else {
crate::leanh::lean_inc(v_a_5960_);
crate::leanh::lean_dec(v___x_5959_);
v___x_5962_ = crate::leanh::lean_box(0);
v_isShared_5963_ = v_isSharedCheck_5969_;
state = 65; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5959_) == 0 {
crate::leanh::lean_dec(v_a_5957_);
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5970_ = crate::leanh::lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_5977_ = (!crate::leanh::lean_is_exclusive(v___x_5959_)) as u8;
if v_isSharedCheck_5977_ == 0 {
v___x_5972_ = v___x_5959_;
v_isShared_5973_ = v_isSharedCheck_5977_;
state = 67; continue;
} else {
crate::leanh::lean_inc(v_a_5970_);
crate::leanh::lean_dec(v___x_5959_);
v___x_5972_ = crate::leanh::lean_box(0);
v_isShared_5973_ = v_isSharedCheck_5977_;
state = 67; continue;
}
} else {
v_a_5978_ = crate::leanh::lean_ctor_get(v___x_5959_, 0);
crate::leanh::lean_inc(v_a_5978_);
crate::leanh::lean_dec_ref_known(v___x_5959_, 1);
v___x_5979_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17;
crate::leanh::lean_inc(v_json_5621_);
v___x_5980_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_json_5621_, v___x_5979_);
if crate::leanh::lean_obj_tag(v___x_5980_) == 0 {
crate::leanh::lean_dec(v_a_5978_);
crate::leanh::lean_dec(v_a_5957_);
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5981_ = crate::leanh::lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_5990_ = (!crate::leanh::lean_is_exclusive(v___x_5980_)) as u8;
if v_isSharedCheck_5990_ == 0 {
v___x_5983_ = v___x_5980_;
v_isShared_5984_ = v_isSharedCheck_5990_;
state = 69; continue;
} else {
crate::leanh::lean_inc(v_a_5981_);
crate::leanh::lean_dec(v___x_5980_);
v___x_5983_ = crate::leanh::lean_box(0);
v_isShared_5984_ = v_isSharedCheck_5990_;
state = 69; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5980_) == 0 {
crate::leanh::lean_dec(v_a_5978_);
crate::leanh::lean_dec(v_a_5957_);
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
crate::leanh::lean_dec(v_json_5621_);
v_a_5991_ = crate::leanh::lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_5998_ = (!crate::leanh::lean_is_exclusive(v___x_5980_)) as u8;
if v_isSharedCheck_5998_ == 0 {
v___x_5993_ = v___x_5980_;
v_isShared_5994_ = v_isSharedCheck_5998_;
state = 71; continue;
} else {
crate::leanh::lean_inc(v_a_5991_);
crate::leanh::lean_dec(v___x_5980_);
v___x_5993_ = crate::leanh::lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
state = 71; continue;
}
} else {
v_a_5999_ = crate::leanh::lean_ctor_get(v___x_5980_, 0);
crate::leanh::lean_inc(v_a_5999_);
crate::leanh::lean_dec_ref_known(v___x_5980_, 1);
v___x_6000_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18;
v___x_6001_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_json_5621_, v___x_6000_);
if crate::leanh::lean_obj_tag(v___x_6001_) == 0 {
crate::leanh::lean_dec(v_a_5999_);
crate::leanh::lean_dec(v_a_5978_);
crate::leanh::lean_dec(v_a_5957_);
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
v_a_6002_ = crate::leanh::lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6011_ = (!crate::leanh::lean_is_exclusive(v___x_6001_)) as u8;
if v_isSharedCheck_6011_ == 0 {
v___x_6004_ = v___x_6001_;
v_isShared_6005_ = v_isSharedCheck_6011_;
state = 73; continue;
} else {
crate::leanh::lean_inc(v_a_6002_);
crate::leanh::lean_dec(v___x_6001_);
v___x_6004_ = crate::leanh::lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6011_;
state = 73; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_6001_) == 0 {
crate::leanh::lean_dec(v_a_5999_);
crate::leanh::lean_dec(v_a_5978_);
crate::leanh::lean_dec(v_a_5957_);
crate::leanh::lean_dec(v_a_5936_);
crate::leanh::lean_dec(v_a_5915_);
crate::leanh::lean_dec(v_a_5894_);
crate::leanh::lean_dec(v_a_5873_);
crate::leanh::lean_dec(v_a_5852_);
crate::leanh::lean_dec(v_a_5831_);
crate::leanh::lean_dec(v_a_5810_);
crate::leanh::lean_dec(v_a_5789_);
crate::leanh::lean_dec(v_a_5768_);
crate::leanh::lean_dec(v_a_5747_);
crate::leanh::lean_dec(v_a_5726_);
crate::leanh::lean_dec(v_a_5705_);
crate::leanh::lean_dec(v_a_5684_);
crate::leanh::lean_dec(v_a_5663_);
crate::leanh::lean_dec(v_a_5642_);
v_a_6012_ = crate::leanh::lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6019_ = (!crate::leanh::lean_is_exclusive(v___x_6001_)) as u8;
if v_isSharedCheck_6019_ == 0 {
v___x_6014_ = v___x_6001_;
v_isShared_6015_ = v_isSharedCheck_6019_;
state = 75; continue;
} else {
crate::leanh::lean_inc(v_a_6012_);
crate::leanh::lean_dec(v___x_6001_);
v___x_6014_ = crate::leanh::lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6019_;
state = 75; continue;
}
} else {
v_a_6020_ = crate::leanh::lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6038_ = (!crate::leanh::lean_is_exclusive(v___x_6001_)) as u8;
if v_isSharedCheck_6038_ == 0 {
v___x_6022_ = v___x_6001_;
v_isShared_6023_ = v_isSharedCheck_6038_;
state = 77; continue;
} else {
crate::leanh::lean_inc(v_a_6020_);
crate::leanh::lean_dec(v___x_6001_);
v___x_6022_ = crate::leanh::lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6038_;
state = 77; continue;
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
                v___x_5628_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8,
                );
                v___x_5629_ = lean_string_append(v___x_5628_, v_a_5624_);
                crate::leanh::lean_dec(v_a_5624_);
                if v_isShared_5627_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5626_, 0, v___x_5629_);
                    v___x_5631_ = v___x_5626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5632_, 0, v___x_5629_);
                    v___x_5631_ = v_reuseFailAlloc_5632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5631_;
            }
            3 => {
                if v_isShared_5637_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5636_, 0);
                    v___x_5639_ = v___x_5636_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
                    v___x_5639_ = v_reuseFailAlloc_5640_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5639_;
            }
            5 => {
                v___x_5649_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13,
                );
                v___x_5650_ = lean_string_append(v___x_5649_, v_a_5645_);
                crate::leanh::lean_dec(v_a_5645_);
                if v_isShared_5648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5647_, 0, v___x_5650_);
                    v___x_5652_ = v___x_5647_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5653_, 0, v___x_5650_);
                    v___x_5652_ = v_reuseFailAlloc_5653_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5652_;
            }
            7 => {
                if v_isShared_5658_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5657_, 0);
                    v___x_5660_ = v___x_5657_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_a_5655_);
                    v___x_5660_ = v_reuseFailAlloc_5661_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5660_;
            }
            9 => {
                v___x_5670_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17,
                );
                v___x_5671_ = lean_string_append(v___x_5670_, v_a_5666_);
                crate::leanh::lean_dec(v_a_5666_);
                if v_isShared_5669_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5668_, 0, v___x_5671_);
                    v___x_5673_ = v___x_5668_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v___x_5671_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5673_;
            }
            11 => {
                if v_isShared_5679_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5678_, 0);
                    v___x_5681_ = v___x_5678_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5676_);
                    v___x_5681_ = v_reuseFailAlloc_5682_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5681_;
            }
            13 => {
                v___x_5691_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21,
                );
                v___x_5692_ = lean_string_append(v___x_5691_, v_a_5687_);
                crate::leanh::lean_dec(v_a_5687_);
                if v_isShared_5690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5689_, 0, v___x_5692_);
                    v___x_5694_ = v___x_5689_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5692_);
                    v___x_5694_ = v_reuseFailAlloc_5695_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5694_;
            }
            15 => {
                if v_isShared_5700_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5699_, 0);
                    v___x_5702_ = v___x_5699_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5697_);
                    v___x_5702_ = v_reuseFailAlloc_5703_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5702_;
            }
            17 => {
                v___x_5712_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25,
                );
                v___x_5713_ = lean_string_append(v___x_5712_, v_a_5708_);
                crate::leanh::lean_dec(v_a_5708_);
                if v_isShared_5711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5710_, 0, v___x_5713_);
                    v___x_5715_ = v___x_5710_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
                    v___x_5715_ = v_reuseFailAlloc_5716_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5715_;
            }
            19 => {
                if v_isShared_5721_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5720_, 0);
                    v___x_5723_ = v___x_5720_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5718_);
                    v___x_5723_ = v_reuseFailAlloc_5724_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5723_;
            }
            21 => {
                v___x_5733_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29,
                );
                v___x_5734_ = lean_string_append(v___x_5733_, v_a_5729_);
                crate::leanh::lean_dec(v_a_5729_);
                if v_isShared_5732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5731_, 0, v___x_5734_);
                    v___x_5736_ = v___x_5731_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5734_);
                    v___x_5736_ = v_reuseFailAlloc_5737_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5736_;
            }
            23 => {
                if v_isShared_5742_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5741_, 0);
                    v___x_5744_ = v___x_5741_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5739_);
                    v___x_5744_ = v_reuseFailAlloc_5745_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5744_;
            }
            25 => {
                v___x_5754_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33,
                );
                v___x_5755_ = lean_string_append(v___x_5754_, v_a_5750_);
                crate::leanh::lean_dec(v_a_5750_);
                if v_isShared_5753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5752_, 0, v___x_5755_);
                    v___x_5757_ = v___x_5752_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 0, v___x_5755_);
                    v___x_5757_ = v_reuseFailAlloc_5758_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5757_;
            }
            27 => {
                if v_isShared_5763_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5762_, 0);
                    v___x_5765_ = v___x_5762_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5766_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
                    v___x_5765_ = v_reuseFailAlloc_5766_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5765_;
            }
            29 => {
                v___x_5775_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37,
                );
                v___x_5776_ = lean_string_append(v___x_5775_, v_a_5771_);
                crate::leanh::lean_dec(v_a_5771_);
                if v_isShared_5774_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5773_, 0, v___x_5776_);
                    v___x_5778_ = v___x_5773_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 0, v___x_5776_);
                    v___x_5778_ = v_reuseFailAlloc_5779_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5778_;
            }
            31 => {
                if v_isShared_5784_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5783_, 0);
                    v___x_5786_ = v___x_5783_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_a_5781_);
                    v___x_5786_ = v_reuseFailAlloc_5787_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5786_;
            }
            33 => {
                v___x_5796_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41,
                );
                v___x_5797_ = lean_string_append(v___x_5796_, v_a_5792_);
                crate::leanh::lean_dec(v_a_5792_);
                if v_isShared_5795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5794_, 0, v___x_5797_);
                    v___x_5799_ = v___x_5794_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5800_, 0, v___x_5797_);
                    v___x_5799_ = v_reuseFailAlloc_5800_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5799_;
            }
            35 => {
                if v_isShared_5805_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5804_, 0);
                    v___x_5807_ = v___x_5804_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_a_5802_);
                    v___x_5807_ = v_reuseFailAlloc_5808_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5807_;
            }
            37 => {
                v___x_5817_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45,
                );
                v___x_5818_ = lean_string_append(v___x_5817_, v_a_5813_);
                crate::leanh::lean_dec(v_a_5813_);
                if v_isShared_5816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5815_, 0, v___x_5818_);
                    v___x_5820_ = v___x_5815_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5821_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5821_, 0, v___x_5818_);
                    v___x_5820_ = v_reuseFailAlloc_5821_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5820_;
            }
            39 => {
                if v_isShared_5826_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5825_, 0);
                    v___x_5828_ = v___x_5825_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5823_);
                    v___x_5828_ = v_reuseFailAlloc_5829_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5828_;
            }
            41 => {
                v___x_5838_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50,
                );
                v___x_5839_ = lean_string_append(v___x_5838_, v_a_5834_);
                crate::leanh::lean_dec(v_a_5834_);
                if v_isShared_5837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5836_, 0, v___x_5839_);
                    v___x_5841_ = v___x_5836_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5839_);
                    v___x_5841_ = v_reuseFailAlloc_5842_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5841_;
            }
            43 => {
                if v_isShared_5847_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5846_, 0);
                    v___x_5849_ = v___x_5846_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
                    v___x_5849_ = v_reuseFailAlloc_5850_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_5849_;
            }
            45 => {
                v___x_5859_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54,
                );
                v___x_5860_ = lean_string_append(v___x_5859_, v_a_5855_);
                crate::leanh::lean_dec(v_a_5855_);
                if v_isShared_5858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5857_, 0, v___x_5860_);
                    v___x_5862_ = v___x_5857_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 0, v___x_5860_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5862_;
            }
            47 => {
                if v_isShared_5868_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5867_, 0);
                    v___x_5870_ = v___x_5867_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5871_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_a_5865_);
                    v___x_5870_ = v_reuseFailAlloc_5871_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5870_;
            }
            49 => {
                v___x_5880_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58,
                );
                v___x_5881_ = lean_string_append(v___x_5880_, v_a_5876_);
                crate::leanh::lean_dec(v_a_5876_);
                if v_isShared_5879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5878_, 0, v___x_5881_);
                    v___x_5883_ = v___x_5878_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5881_);
                    v___x_5883_ = v_reuseFailAlloc_5884_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5883_;
            }
            51 => {
                if v_isShared_5889_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5888_, 0);
                    v___x_5891_ = v___x_5888_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5892_, 0, v_a_5886_);
                    v___x_5891_ = v_reuseFailAlloc_5892_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5891_;
            }
            53 => {
                v___x_5901_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63,
                );
                v___x_5902_ = lean_string_append(v___x_5901_, v_a_5897_);
                crate::leanh::lean_dec(v_a_5897_);
                if v_isShared_5900_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5899_, 0, v___x_5902_);
                    v___x_5904_ = v___x_5899_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5905_, 0, v___x_5902_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5904_;
            }
            55 => {
                if v_isShared_5910_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5909_, 0);
                    v___x_5912_ = v___x_5909_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5907_);
                    v___x_5912_ = v_reuseFailAlloc_5913_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_5912_;
            }
            57 => {
                v___x_5922_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68,
                );
                v___x_5923_ = lean_string_append(v___x_5922_, v_a_5918_);
                crate::leanh::lean_dec(v_a_5918_);
                if v_isShared_5921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5920_, 0, v___x_5923_);
                    v___x_5925_ = v___x_5920_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5923_);
                    v___x_5925_ = v_reuseFailAlloc_5926_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_5925_;
            }
            59 => {
                if v_isShared_5931_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5930_, 0);
                    v___x_5933_ = v___x_5930_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_5934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5934_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_5933_;
            }
            61 => {
                v___x_5943_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73,
                );
                v___x_5944_ = lean_string_append(v___x_5943_, v_a_5939_);
                crate::leanh::lean_dec(v_a_5939_);
                if v_isShared_5942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5941_, 0, v___x_5944_);
                    v___x_5946_ = v___x_5941_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5947_, 0, v___x_5944_);
                    v___x_5946_ = v_reuseFailAlloc_5947_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_5946_;
            }
            63 => {
                if v_isShared_5952_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5951_, 0);
                    v___x_5954_ = v___x_5951_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5955_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_a_5949_);
                    v___x_5954_ = v_reuseFailAlloc_5955_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_5954_;
            }
            65 => {
                v___x_5964_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78,
                );
                v___x_5965_ = lean_string_append(v___x_5964_, v_a_5960_);
                crate::leanh::lean_dec(v_a_5960_);
                if v_isShared_5963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5962_, 0, v___x_5965_);
                    v___x_5967_ = v___x_5962_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_5968_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 0, v___x_5965_);
                    v___x_5967_ = v_reuseFailAlloc_5968_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_5967_;
            }
            67 => {
                if v_isShared_5973_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5972_, 0);
                    v___x_5975_ = v___x_5972_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_5976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_a_5970_);
                    v___x_5975_ = v_reuseFailAlloc_5976_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_5975_;
            }
            69 => {
                v___x_5985_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83,
                );
                v___x_5986_ = lean_string_append(v___x_5985_, v_a_5981_);
                crate::leanh::lean_dec(v_a_5981_);
                if v_isShared_5984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5983_, 0, v___x_5986_);
                    v___x_5988_ = v___x_5983_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_5988_;
            }
            71 => {
                if v_isShared_5994_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5993_, 0);
                    v___x_5996_ = v___x_5993_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_5997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
                    v___x_5996_ = v_reuseFailAlloc_5997_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_5996_;
            }
            73 => {
                v___x_6006_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88,
                );
                v___x_6007_ = lean_string_append(v___x_6006_, v_a_6002_);
                crate::leanh::lean_dec(v_a_6002_);
                if v_isShared_6005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6004_, 0, v___x_6007_);
                    v___x_6009_ = v___x_6004_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_6010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6010_, 0, v___x_6007_);
                    v___x_6009_ = v_reuseFailAlloc_6010_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_6009_;
            }
            75 => {
                if v_isShared_6015_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6014_, 0);
                    v___x_6017_ = v___x_6014_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_6018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
                    v___x_6017_ = v_reuseFailAlloc_6018_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_6017_;
            }
            77 => {
                v___x_6024_ = crate::leanh::lean_alloc_ctor(0, 9, (10) as u32);
                crate::leanh::lean_ctor_set(v___x_6024_, 0, v_a_5642_);
                crate::leanh::lean_ctor_set(v___x_6024_, 1, v_a_5663_);
                crate::leanh::lean_ctor_set(v___x_6024_, 2, v_a_5852_);
                crate::leanh::lean_ctor_set(v___x_6024_, 3, v_a_5915_);
                crate::leanh::lean_ctor_set(v___x_6024_, 4, v_a_5936_);
                crate::leanh::lean_ctor_set(v___x_6024_, 5, v_a_5957_);
                crate::leanh::lean_ctor_set(v___x_6024_, 6, v_a_5978_);
                crate::leanh::lean_ctor_set(v___x_6024_, 7, v_a_5999_);
                crate::leanh::lean_ctor_set(v___x_6024_, 8, v_a_6020_);
                v___x_6025_ = (crate::leanh::lean_unbox(v_a_5684_) as u8);
                crate::leanh::lean_dec(v_a_5684_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    v___x_6025_,
                );
                v___x_6026_ = (crate::leanh::lean_unbox(v_a_5705_) as u8);
                crate::leanh::lean_dec(v_a_5705_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                    v___x_6026_,
                );
                v___x_6027_ = (crate::leanh::lean_unbox(v_a_5726_) as u8);
                crate::leanh::lean_dec(v_a_5726_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                    v___x_6027_,
                );
                v___x_6028_ = (crate::leanh::lean_unbox(v_a_5747_) as u8);
                crate::leanh::lean_dec(v_a_5747_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 3) as u32,
                    v___x_6028_,
                );
                v___x_6029_ = (crate::leanh::lean_unbox(v_a_5768_) as u8);
                crate::leanh::lean_dec(v_a_5768_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 4) as u32,
                    v___x_6029_,
                );
                v___x_6030_ = (crate::leanh::lean_unbox(v_a_5789_) as u8);
                crate::leanh::lean_dec(v_a_5789_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 5) as u32,
                    v___x_6030_,
                );
                v___x_6031_ = (crate::leanh::lean_unbox(v_a_5810_) as u8);
                crate::leanh::lean_dec(v_a_5810_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 6) as u32,
                    v___x_6031_,
                );
                v___x_6032_ = (crate::leanh::lean_unbox(v_a_5831_) as u8);
                crate::leanh::lean_dec(v_a_5831_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 7) as u32,
                    v___x_6032_,
                );
                v___x_6033_ = (crate::leanh::lean_unbox(v_a_5873_) as u8);
                crate::leanh::lean_dec(v_a_5873_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 8) as u32,
                    v___x_6033_,
                );
                v___x_6034_ = (crate::leanh::lean_unbox(v_a_5894_) as u8);
                crate::leanh::lean_dec(v_a_5894_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 9) as u32,
                    v___x_6034_,
                );
                if v_isShared_6023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6022_, 0, v___x_6024_);
                    v___x_6036_ = v___x_6022_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_6037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6024_);
                    v___x_6036_ = v_reuseFailAlloc_6037_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                return v___x_6036_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Capabilities(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_JsonRpc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_CodeActions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Capabilities(
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
pub unsafe fn initialize_Lean_Data_Lsp_Capabilities(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_JsonRpc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_CodeActions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Capabilities(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Capabilities(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Capabilities(builtin);
}
