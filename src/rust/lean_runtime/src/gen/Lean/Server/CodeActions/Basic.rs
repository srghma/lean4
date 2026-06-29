// Lean compiler output
// Module: Lean.Server.CodeActions.Basic
// Imports: Lean.Server.Requests
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_zip___redArg,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr3, l_Lean_replaceRef};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_ensureAttrDeclIsMeta,
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::InitAttr::l_Lean_declareBuiltin;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Name_fromJson_x3f;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Lsp::CodeActions::{
    l_Lean_Lsp_instFromJsonCodeAction_fromJson, l_Lean_Lsp_instFromJsonCodeActionParams_fromJson,
    l_Lean_Lsp_instToJsonCodeAction_toJson, l_Lean_Lsp_instToJsonCodeActionParams_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_lspPosToUtf8Pos;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_evalConstCheck___redArg,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_isConstOf, l_Lean_mkAppB, l_Lean_mkConst};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_evalConstCheck___redArg;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Server::Requests::{
    initialize_Lean_Server_Requests, l_Lean_Server_RequestError_internalError,
    l_Lean_Server_RequestError_invalidParams, l_Lean_Server_RequestError_ofIoError,
    l_Lean_Server_RequestM_checkCancelled, l_Lean_Server_RequestM_runCoreM___redArg,
    l_Lean_Server_RequestM_withWaitFindSnap___redArg,
    l_Lean_Server_instInhabitedRequestError_default, l_Lean_Server_requestHandlers,
    runtime_initialize_Lean_Server_Requests,
};
use crate::r#gen::Lean::Server::ServerTask::l_Lean_Server_ServerTask_mapCheap___redArg;
use crate::r#gen::Lean::Server::Snapshots::l_Lean_Server_Snapshots_Snapshot_endPos;
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_hash,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::MonadEnv::lean_has_compile_error;
pub static l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0_value:
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
    m_data: [112, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1_value:
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
    m_data: [112, 114, 111, 118, 105, 100, 101, 114, 78, 97, 109, 101, 0],
};
static mut l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2_value:
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
        112, 114, 111, 118, 105, 100, 101, 114, 82, 101, 115, 117, 108, 116, 73, 110, 100, 101,
        120, 0,
    ],
};
static mut l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3_value:
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
static mut l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonCodeActionResolveData___closed__0_value:
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
    m_fun: l_Lean_Server_instToJsonCodeActionResolveData_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instToJsonCodeActionResolveData___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instToJsonCodeActionResolveData: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value:
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
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value:
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
    m_data: [83, 101, 114, 118, 101, 114, 0],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2_value:
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
        67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 82, 101, 115, 111, 108, 118, 101, 68, 97,
        116, 97, 0,
    ],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_0:
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
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_1:
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
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value:
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
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16698149290437747497 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5_value:
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
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11778480723588288892 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10_value:
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
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10721213016902645152 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1570459047818708292 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instFromJsonCodeActionResolveData___closed__0_value:
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
    m_fun: l_Lean_Server_instFromJsonCodeActionResolveData_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instFromJsonCodeActionResolveData___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instFromJsonCodeActionResolveData: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_CodeAction_getFileSource_x21___closed__0_value:
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
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 67, 111, 100, 101, 65, 99, 116, 105,
        111, 110, 115, 46, 66, 97, 115, 105, 99, 0,
    ],
};
static mut l_Lean_Server_CodeAction_getFileSource_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_CodeAction_getFileSource_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_CodeAction_getFileSource_x21___closed__1_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 67, 111, 100, 101, 65, 99, 116, 105,
        111, 110, 46, 103, 101, 116, 70, 105, 108, 101, 83, 111, 117, 114, 99, 101, 33, 0,
    ],
};
static mut l_Lean_Server_CodeAction_getFileSource_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_CodeAction_getFileSource_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_CodeAction_getFileSource_x21___closed__2_value:
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
        110, 111, 32, 100, 97, 116, 97, 32, 112, 97, 114, 97, 109, 32, 111, 110, 32, 99, 111, 100,
        101, 32, 97, 99, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Server_CodeAction_getFileSource_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_CodeAction_getFileSource_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFileSourceCodeAction___closed__0_value:
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
    m_fun: l_Lean_Server_CodeAction_getFileSource_x21 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instFileSourceCodeAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFileSourceCodeAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instFileSourceCodeAction: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFileSourceCodeAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0_value:
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
    m_fun: l_Lean_Server_instCoeCodeActionLazyCodeAction___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instCoeCodeActionLazyCodeAction: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instCoeCodeActionLazyCodeAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instInhabitedCodeActionProvider___closed__0_value:
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
    m_fun: l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instInhabitedCodeActionProvider___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedCodeActionProvider___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instInhabitedCodeActionProvider: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedCodeActionProvider___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_NameSet_insert as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 69, 120, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10268502111126431744 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_codeActionProviderExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [93, 96, 58, 32, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [96, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [10, 98, 117, 116, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [93, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 97, 100, 100, 101, 100, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 111, 102, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [97, 100, 100, 66, 117, 105, 108, 116, 105, 110, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5949480926448383572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,12337524736695414095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17302608593553616169 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__5_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8706487141215280158 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__7_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10287005189753007335 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__8_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,15763962247737354970 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__9_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,6155145710909489103 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__10_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__11_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6217912240122920526 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__12_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__13_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5336046295118102095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__14_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,14208547614659458146 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__15_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,2453617526053248327 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__16_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__4_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2937448598322842065 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__17_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__6_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1186726535977104182 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__18_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1656927832 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,11600860958007092115 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__19_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__20_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3169724506793087048 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__21_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__22_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10704921703733883212 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__23_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16003643713111172725 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<108> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 108, m_capacity: 108, m_length: 107, m_data: [85, 115, 101, 32, 116, 111, 32, 100, 101, 99, 111, 114, 97, 116, 101, 32, 109, 101, 116, 104, 111, 100, 115, 32, 102, 111, 114, 32, 115, 117, 103, 103, 101, 115, 116, 105, 110, 103, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 108, 111, 119, 45, 108, 101, 118, 101, 108, 32, 105, 110, 116, 101, 114, 102, 97, 99, 101, 32, 102, 111, 114, 32, 109, 97, 107, 105, 110, 103, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 46, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [40, 98, 117, 105, 108, 116, 105, 110, 41, 32, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 95, 112, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1789645175004858789 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 95, 112, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9238980665832387105 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2747767106885577070 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_handleCodeAction___lam__1___closed__0_value:
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
static mut l_Lean_Server_handleCodeAction___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeAction___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleCodeAction___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Server_handleCodeAction___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Server_handleCodeAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleCodeAction___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Server_handleCodeAction___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeAction___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleCodeAction___closed__2_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Server_handleCodeAction___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Server_handleCodeAction___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_handleCodeAction___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeAction___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 114, 101, 113, 117, 101, 115, 116, 32, 112, 97, 114, 97, 109, 115, 58, 32, 0]};
static mut l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114, 32, 39, 0]};
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [39, 58, 32, 111, 110, 108, 121, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [39, 58, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0]};
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 47, 99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_handleCodeAction___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleCodeActionResolve___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 115, 111, 108, 118, 101, 32, 99,
        111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 32, 105, 110, 100, 101, 120, 32, 0,
    ],
};
static mut l_Lean_Server_handleCodeActionResolve___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeActionResolve___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleCodeActionResolve___closed__0_value: crate::leanh::LeanStringObject<
    19,
> = crate::leanh::LeanStringObject {
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
        115, 110, 97, 112, 115, 104, 111, 116, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0,
    ],
};
static mut l_Lean_Server_handleCodeActionResolve___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeActionResolve___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_handleCodeActionResolve___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_handleCodeActionResolve___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_handleCodeActionResolve___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_handleCodeActionResolve___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_handleCodeActionResolve___closed__3_value: crate::leanh::LeanStringObject<
    37,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 100, 97, 116, 97, 32, 102, 105, 101, 108,
        100, 32, 111, 110, 32, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 46, 0,
    ],
};
static mut l_Lean_Server_handleCodeActionResolve___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleCodeActionResolve___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_handleCodeActionResolve___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_handleCodeActionResolve___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [99, 111, 100, 101, 65, 99, 116, 105, 111, 110, 47, 114, 101, 115, 111, 108, 118, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_handleCodeActionResolve___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonCodeActionResolveData_toJson_spec__0(
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2732_) == 0 {
                    v___x_2734_ = lean_array_to_list(v_a_2733_);
                    return v___x_2734_;
                } else {
                    v_head_2735_ = crate::leanh::lean_ctor_get(v_a_2732_, 0);
                    crate::leanh::lean_inc(v_head_2735_);
                    v_tail_2736_ = crate::leanh::lean_ctor_get(v_a_2732_, 1);
                    crate::leanh::lean_inc(v_tail_2736_);
                    crate::leanh::lean_dec_ref_known(v_a_2732_, 2);
                    v___x_2737_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_2733_,
                        v_head_2735_,
                    );
                    v_a_2732_ = v_tail_2736_;
                    v_a_2733_ = v___x_2737_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instToJsonCodeActionResolveData_toJson(
    mut v_x_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_providerName_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_providerResultIndex_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_params_2745_ = crate::leanh::lean_ctor_get(v_x_2744_, 0);
    crate::leanh::lean_inc_ref(v_params_2745_);
    v_providerName_2746_ = crate::leanh::lean_ctor_get(v_x_2744_, 1);
    crate::leanh::lean_inc(v_providerName_2746_);
    v_providerResultIndex_2747_ = crate::leanh::lean_ctor_get(v_x_2744_, 2);
    crate::leanh::lean_inc(v_providerResultIndex_2747_);
    crate::leanh::lean_dec_ref(v_x_2744_);
    v___x_2748_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0;
    v___x_2749_ = l_Lean_Lsp_instToJsonCodeActionParams_toJson(v_params_2745_);
    v___x_2750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2748_);
    crate::leanh::lean_ctor_set(v___x_2750_, 1, v___x_2749_);
    v___x_2751_ = crate::leanh::lean_box(0);
    v___x_2752_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2752_, 0, v___x_2750_);
    crate::leanh::lean_ctor_set(v___x_2752_, 1, v___x_2751_);
    v___x_2753_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1;
    v___x_2754_ = 1;
    v___x_2755_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_providerName_2746_,
        v___x_2754_,
    );
    v___x_2756_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2756_, 0, v___x_2755_);
    v___x_2757_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2753_);
    crate::leanh::lean_ctor_set(v___x_2757_, 1, v___x_2756_);
    v___x_2758_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2758_, 0, v___x_2757_);
    crate::leanh::lean_ctor_set(v___x_2758_, 1, v___x_2751_);
    v___x_2759_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2;
    v___x_2760_ = l_Lean_JsonNumber_fromNat(v_providerResultIndex_2747_);
    v___x_2761_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2761_, 0, v___x_2760_);
    v___x_2762_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2762_, 0, v___x_2759_);
    crate::leanh::lean_ctor_set(v___x_2762_, 1, v___x_2761_);
    v___x_2763_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2763_, 0, v___x_2762_);
    crate::leanh::lean_ctor_set(v___x_2763_, 1, v___x_2751_);
    v___x_2764_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2764_, 0, v___x_2763_);
    crate::leanh::lean_ctor_set(v___x_2764_, 1, v___x_2751_);
    v___x_2765_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2765_, 0, v___x_2758_);
    crate::leanh::lean_ctor_set(v___x_2765_, 1, v___x_2764_);
    v___x_2766_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2766_, 0, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2766_, 1, v___x_2765_);
    v___x_2767_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__3;
    v___x_2768_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonCodeActionResolveData_toJson_spec__0(v___x_2766_, v___x_2767_);
    v___x_2769_ = l_Lean_Json_mkObj(v___x_2768_);
    crate::leanh::lean_dec(v___x_2768_);
    return v___x_2769_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(
    mut v_j_2772_: *mut crate::leanh::LeanObject,
    mut v_k_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2774_ = l_Lean_Json_getObjValD(v_j_2772_, v_k_2773_);
    v___x_2775_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(v___x_2774_);
    return v___x_2775_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0___boxed(
    mut v_j_2776_: *mut crate::leanh::LeanObject,
    mut v_k_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(v_j_2776_, v_k_2777_);
    crate::leanh::lean_dec_ref(v_k_2777_);
    return v_res_2778_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(
    mut v_j_2779_: *mut crate::leanh::LeanObject,
    mut v_k_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2781_ = l_Lean_Json_getObjValD(v_j_2779_, v_k_2780_);
    v___x_2782_ = l_Lean_Name_fromJson_x3f(v___x_2781_);
    return v___x_2782_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1___boxed(
    mut v_j_2783_: *mut crate::leanh::LeanObject,
    mut v_k_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(v_j_2783_, v_k_2784_);
    crate::leanh::lean_dec_ref(v_k_2784_);
    return v_res_2785_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(
    mut v_j_2786_: *mut crate::leanh::LeanObject,
    mut v_k_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2788_ = l_Lean_Json_getObjValD(v_j_2786_, v_k_2787_);
    v___x_2789_ = l_Lean_Json_getNat_x3f(v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2___boxed(
    mut v_j_2790_: *mut crate::leanh::LeanObject,
    mut v_k_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(v_j_2790_, v_k_2791_);
    crate::leanh::lean_dec_ref(v_k_2791_);
    return v_res_2792_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = 1;
    v___x_2801_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__3;
    v___x_2802_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2801_, v___x_2800_);
    return v___x_2802_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2804_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5;
    v___x_2805_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__4,
    );
    v___x_2806_ = lean_string_append(v___x_2805_, v___x_2804_);
    return v___x_2806_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2809_ = 1;
    v___x_2810_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__7;
    v___x_2811_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2810_, v___x_2809_);
    return v___x_2811_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2812_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__8,
    );
    v___x_2813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6,
    );
    v___x_2814_ = lean_string_append(v___x_2813_, v___x_2812_);
    return v___x_2814_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2816_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10;
    v___x_2817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__9,
    );
    v___x_2818_ = lean_string_append(v___x_2817_, v___x_2816_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2821_ = 1;
    v___x_2822_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__12;
    v___x_2823_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2822_, v___x_2821_);
    return v___x_2823_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__13,
    );
    v___x_2825_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6,
    );
    v___x_2826_ = lean_string_append(v___x_2825_, v___x_2824_);
    return v___x_2826_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10;
    v___x_2828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__14,
    );
    v___x_2829_ = lean_string_append(v___x_2828_, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = 1;
    v___x_2833_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__16;
    v___x_2834_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2833_, v___x_2832_);
    return v___x_2834_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__17,
    );
    v___x_2836_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__6,
    );
    v___x_2837_ = lean_string_append(v___x_2836_, v___x_2835_);
    return v___x_2837_;
}
pub unsafe fn _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2838_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__10;
    v___x_2839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18_once
        ),
        _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__18,
    );
    v___x_2840_ = lean_string_append(v___x_2839_, v___x_2838_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(
    mut v_json_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2847_: u8 = 0;
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2853_: u8 = 0;
    let mut v_a_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_a_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2874_: u8 = 0;
    let mut v_a_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_a_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v_a_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_a_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2842_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__0;
                crate::leanh::lean_inc(v_json_2841_);
                v___x_2843_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__0(v_json_2841_, v___x_2842_);
                if crate::leanh::lean_obj_tag(v___x_2843_) == 0 {
                    crate::leanh::lean_dec(v_json_2841_);
                    v_a_2844_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                    v_isSharedCheck_2853_ = (!crate::leanh::lean_is_exclusive(v___x_2843_)) as u8;
                    if v_isSharedCheck_2853_ == 0 {
                        v___x_2846_ = v___x_2843_;
                        v_isShared_2847_ = v_isSharedCheck_2853_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2844_);
                        crate::leanh::lean_dec(v___x_2843_);
                        v___x_2846_ = crate::leanh::lean_box(0);
                        v_isShared_2847_ = v_isSharedCheck_2853_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2843_) == 0 {
                        crate::leanh::lean_dec(v_json_2841_);
                        v_a_2854_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                        v_isSharedCheck_2861_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2843_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v___x_2856_ = v___x_2843_;
                            v_isShared_2857_ = v_isSharedCheck_2861_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2854_);
                            crate::leanh::lean_dec(v___x_2843_);
                            v___x_2856_ = crate::leanh::lean_box(0);
                            v_isShared_2857_ = v_isSharedCheck_2861_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2862_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                        crate::leanh::lean_inc(v_a_2862_);
                        crate::leanh::lean_dec_ref_known(v___x_2843_, 1);
                        v___x_2863_ =
                            l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_2841_);
                        v___x_2864_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__1(v_json_2841_, v___x_2863_);
                        if crate::leanh::lean_obj_tag(v___x_2864_) == 0 {
                            crate::leanh::lean_dec(v_a_2862_);
                            crate::leanh::lean_dec(v_json_2841_);
                            v_a_2865_ = crate::leanh::lean_ctor_get(v___x_2864_, 0);
                            v_isSharedCheck_2874_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2864_)) as u8;
                            if v_isSharedCheck_2874_ == 0 {
                                v___x_2867_ = v___x_2864_;
                                v_isShared_2868_ = v_isSharedCheck_2874_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2865_);
                                crate::leanh::lean_dec(v___x_2864_);
                                v___x_2867_ = crate::leanh::lean_box(0);
                                v_isShared_2868_ = v_isSharedCheck_2874_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2864_) == 0 {
                                crate::leanh::lean_dec(v_a_2862_);
                                crate::leanh::lean_dec(v_json_2841_);
                                v_a_2875_ = crate::leanh::lean_ctor_get(v___x_2864_, 0);
                                v_isSharedCheck_2882_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2864_)) as u8;
                                if v_isSharedCheck_2882_ == 0 {
                                    v___x_2877_ = v___x_2864_;
                                    v_isShared_2878_ = v_isSharedCheck_2882_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2875_);
                                    crate::leanh::lean_dec(v___x_2864_);
                                    v___x_2877_ = crate::leanh::lean_box(0);
                                    v_isShared_2878_ = v_isSharedCheck_2882_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2883_ = crate::leanh::lean_ctor_get(v___x_2864_, 0);
                                crate::leanh::lean_inc(v_a_2883_);
                                crate::leanh::lean_dec_ref_known(v___x_2864_, 1);
                                v___x_2884_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson___closed__2;
                                v___x_2885_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonCodeActionResolveData_fromJson_spec__2(v_json_2841_, v___x_2884_);
                                if crate::leanh::lean_obj_tag(v___x_2885_) == 0 {
                                    crate::leanh::lean_dec(v_a_2883_);
                                    crate::leanh::lean_dec(v_a_2862_);
                                    v_a_2886_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                                    v_isSharedCheck_2895_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                                    if v_isSharedCheck_2895_ == 0 {
                                        v___x_2888_ = v___x_2885_;
                                        v_isShared_2889_ = v_isSharedCheck_2895_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2886_);
                                        crate::leanh::lean_dec(v___x_2885_);
                                        v___x_2888_ = crate::leanh::lean_box(0);
                                        v_isShared_2889_ = v_isSharedCheck_2895_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_2885_) == 0 {
                                        crate::leanh::lean_dec(v_a_2883_);
                                        crate::leanh::lean_dec(v_a_2862_);
                                        v_a_2896_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                                        v_isSharedCheck_2903_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                                        if v_isSharedCheck_2903_ == 0 {
                                            v___x_2898_ = v___x_2885_;
                                            v_isShared_2899_ = v_isSharedCheck_2903_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2896_);
                                            crate::leanh::lean_dec(v___x_2885_);
                                            v___x_2898_ = crate::leanh::lean_box(0);
                                            v_isShared_2899_ = v_isSharedCheck_2903_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2904_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                                        v_isSharedCheck_2912_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                                        if v_isSharedCheck_2912_ == 0 {
                                            v___x_2906_ = v___x_2885_;
                                            v_isShared_2907_ = v_isSharedCheck_2912_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2904_);
                                            crate::leanh::lean_dec(v___x_2885_);
                                            v___x_2906_ = crate::leanh::lean_box(0);
                                            v_isShared_2907_ = v_isSharedCheck_2912_;
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
                v___x_2848_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__11,
                );
                v___x_2849_ = lean_string_append(v___x_2848_, v_a_2844_);
                crate::leanh::lean_dec(v_a_2844_);
                if v_isShared_2847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2846_, 0, v___x_2849_);
                    v___x_2851_ = v___x_2846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
                    v___x_2851_ = v_reuseFailAlloc_2852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2851_;
            }
            3 => {
                if v_isShared_2857_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2856_, 0);
                    v___x_2859_ = v___x_2856_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
                    v___x_2859_ = v_reuseFailAlloc_2860_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2859_;
            }
            5 => {
                v___x_2869_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__15,
                );
                v___x_2870_ = lean_string_append(v___x_2869_, v_a_2865_);
                crate::leanh::lean_dec(v_a_2865_);
                if v_isShared_2868_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2867_, 0, v___x_2870_);
                    v___x_2872_ = v___x_2867_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
                    v___x_2872_ = v_reuseFailAlloc_2873_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2872_;
            }
            7 => {
                if v_isShared_2878_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2877_, 0);
                    v___x_2880_ = v___x_2877_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
                    v___x_2880_ = v_reuseFailAlloc_2881_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2880_;
            }
            9 => {
                v___x_2890_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19_once
                    ),
                    _init_l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__19,
                );
                v___x_2891_ = lean_string_append(v___x_2890_, v_a_2886_);
                crate::leanh::lean_dec(v_a_2886_);
                if v_isShared_2889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2891_);
                    v___x_2893_ = v___x_2888_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2893_;
            }
            11 => {
                if v_isShared_2899_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2898_, 0);
                    v___x_2901_ = v___x_2898_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
                    v___x_2901_ = v_reuseFailAlloc_2902_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2901_;
            }
            13 => {
                v___x_2908_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2908_, 0, v_a_2862_);
                crate::leanh::lean_ctor_set(v___x_2908_, 1, v_a_2883_);
                crate::leanh::lean_ctor_set(v___x_2908_, 2, v_a_2904_);
                if v_isShared_2907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2906_, 0, v___x_2908_);
                    v___x_2910_ = v___x_2906_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
                    v___x_2910_ = v_reuseFailAlloc_2911_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(
    mut v_msg_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0;
    v___x_2918_ = lean_panic_fn_borrowed(v___x_2917_, v_msg_2916_);
    return v___x_2918_;
}
pub unsafe fn l_Lean_Server_CodeAction_getFileSource_x21(
    mut v_ca_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_textDocument_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_x3f_2931_ = crate::leanh::lean_ctor_get(v_ca_2922_, 9);
                if crate::leanh::lean_obj_tag(v_data_x3f_2931_) == 1 {
                    crate::leanh::lean_inc_ref(v_data_x3f_2931_);
                    crate::leanh::lean_dec_ref(v_ca_2922_);
                    v_val_2932_ = crate::leanh::lean_ctor_get(v_data_x3f_2931_, 0);
                    crate::leanh::lean_inc(v_val_2932_);
                    crate::leanh::lean_dec_ref_known(v_data_x3f_2931_, 1);
                    v___x_2933_ =
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(v_val_2932_);
                    if crate::leanh::lean_obj_tag(v___x_2933_) == 0 {
                        v_a_2934_ = crate::leanh::lean_ctor_get(v___x_2933_, 0);
                        crate::leanh::lean_inc(v_a_2934_);
                        crate::leanh::lean_dec_ref_known(v___x_2933_, 1);
                        v_a_2924_ = v_a_2934_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2935_ = crate::leanh::lean_ctor_get(v___x_2933_, 0);
                        crate::leanh::lean_inc(v_a_2935_);
                        crate::leanh::lean_dec_ref_known(v___x_2933_, 1);
                        v_params_2936_ = crate::leanh::lean_ctor_get(v_a_2935_, 0);
                        crate::leanh::lean_inc_ref(v_params_2936_);
                        crate::leanh::lean_dec(v_a_2935_);
                        v_textDocument_2937_ = crate::leanh::lean_ctor_get(v_params_2936_, 2);
                        crate::leanh::lean_inc_ref(v_textDocument_2937_);
                        crate::leanh::lean_dec_ref(v_params_2936_);
                        return v_textDocument_2937_;
                    }
                } else {
                    v_title_2938_ = crate::leanh::lean_ctor_get(v_ca_2922_, 2);
                    crate::leanh::lean_inc_ref(v_title_2938_);
                    crate::leanh::lean_dec_ref(v_ca_2922_);
                    v___x_2939_ = l_Lean_Server_CodeAction_getFileSource_x21___closed__2;
                    v___x_2940_ = lean_string_append(v___x_2939_, v_title_2938_);
                    crate::leanh::lean_dec_ref(v_title_2938_);
                    v_a_2924_ = v___x_2940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2925_ = l_Lean_Server_CodeAction_getFileSource_x21___closed__0;
                v___x_2926_ = l_Lean_Server_CodeAction_getFileSource_x21___closed__1;
                v___x_2927_ = crate::leanh::lean_unsigned_to_nat(47);
                v___x_2928_ = crate::leanh::lean_unsigned_to_nat(22);
                v___x_2929_ = l_mkPanicMessageWithDecl(
                    v___x_2925_,
                    v___x_2926_,
                    v___x_2927_,
                    v___x_2928_,
                    v_a_2924_,
                );
                crate::leanh::lean_dec_ref(v_a_2924_);
                v___x_2930_ =
                    l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0(v___x_2929_);
                return v___x_2930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instCoeCodeActionLazyCodeAction___lam__0(
    mut v_c_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2944_ = crate::leanh::lean_box(0);
    v___x_2945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2945_, 0, v_c_2943_);
    crate::leanh::lean_ctor_set(v___x_2945_, 1, v___x_2944_);
    return v___x_2945_;
}
pub unsafe fn l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_2950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2950_, 0, v___x_2949_);
    return v___x_2950_;
}
pub unsafe fn l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg___boxed(
    mut v_a_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ = l_Lean_Server_instInhabitedCodeActionProvider___aux__1___redArg();
    return v_res_2952_;
}
pub unsafe fn l_Lean_Server_instInhabitedCodeActionProvider___aux__1(
    mut v_x_2953_: *mut crate::leanh::LeanObject,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_2958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2958_, 0, v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn l_Lean_Server_instInhabitedCodeActionProvider___aux__1___boxed(
    mut v_x_2959_: *mut crate::leanh::LeanObject,
    mut v_a_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2963_ =
        l_Lean_Server_instInhabitedCodeActionProvider___aux__1(v_x_2959_, v_a_2960_, v_a_2961_);
    crate::leanh::lean_dec_ref(v_a_2961_);
    crate::leanh::lean_dec_ref(v_a_2960_);
    crate::leanh::lean_dec_ref(v_x_2959_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_Server_instInhabitedCodeActionProvider___lam__0(
    mut v___y_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_2969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2969_, 0, v___x_2968_);
    return v___x_2969_;
}
pub unsafe fn l_Lean_Server_instInhabitedCodeActionProvider___lam__0___boxed(
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l_Lean_Server_instInhabitedCodeActionProvider___lam__0(
        v___y_2970_,
        v___y_2971_,
        v___y_2972_,
    );
    crate::leanh::lean_dec_ref(v___y_2972_);
    crate::leanh::lean_dec_ref(v___y_2971_);
    crate::leanh::lean_dec_ref(v___y_2970_);
    return v_res_2974_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2978_ = crate::leanh::lean_box(1);
    v___x_2979_ = lean_st_mk_ref(v___x_2978_);
    v___x_2980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2980_, 0, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2____boxed(
    mut v_a_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
    return v_res_2982_;
}
pub unsafe fn l_Lean_Server_addBuiltinCodeActionProvider(
    mut v_decl_2983_: *mut crate::leanh::LeanObject,
    mut v_provider_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2986_ =
        l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
    v___x_2987_ = lean_st_ref_take(v___x_2986_);
    v___x_2988_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_decl_2983_,
        v_provider_2984_,
        v___x_2987_,
    );
    v___x_2989_ = lean_st_ref_set(v___x_2986_, v___x_2988_);
    v___x_2990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2990_, 0, v___x_2989_);
    return v___x_2990_;
}
pub unsafe fn l_Lean_Server_addBuiltinCodeActionProvider___boxed(
    mut v_decl_2991_: *mut crate::leanh::LeanObject,
    mut v_provider_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_Server_addBuiltinCodeActionProvider(v_decl_2991_, v_provider_2992_);
    return v_res_2994_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(
    mut v_as_2995_: *mut crate::leanh::LeanObject,
    mut v_i_2996_: usize,
    mut v_stop_2997_: usize,
    mut v_b_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2999_ = lean_usize_dec_eq(v_i_2996_, v_stop_2997_);
                if v___x_2999_ == 0 {
                    v___x_3000_ = lean_array_uget_borrowed(v_as_2995_, v_i_2996_);
                    crate::leanh::lean_inc(v___x_3000_);
                    v___x_3001_ = l_Lean_NameSet_insert(v_b_2998_, v___x_3000_);
                    v___x_3002_ = 1usize;
                    v___x_3003_ = lean_usize_add(v_i_2996_, v___x_3002_);
                    v_i_2996_ = v___x_3003_;
                    v_b_2998_ = v___x_3001_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2998_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_3005_: *mut crate::leanh::LeanObject,
    mut v_i_3006_: *mut crate::leanh::LeanObject,
    mut v_stop_3007_: *mut crate::leanh::LeanObject,
    mut v_b_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3009_: usize = 0;
    let mut v_stop_boxed_3010_: usize = 0;
    let mut v_res_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3009_ = crate::leanh::lean_unbox_usize(v_i_3006_);
    crate::leanh::lean_dec(v_i_3006_);
    v_stop_boxed_3010_ = crate::leanh::lean_unbox_usize(v_stop_3007_);
    crate::leanh::lean_dec(v_stop_3007_);
    v_res_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v_as_3005_, v_i_boxed_3009_, v_stop_boxed_3010_, v_b_3008_);
    crate::leanh::lean_dec_ref(v_as_3005_);
    return v_res_3011_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(
    mut v_as_3012_: *mut crate::leanh::LeanObject,
    mut v_i_3013_: usize,
    mut v_stop_3014_: usize,
    mut v_b_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: usize = 0;
    let mut v___x_3019_: usize = 0;
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: usize = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: usize = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3021_ = lean_usize_dec_eq(v_i_3013_, v_stop_3014_);
                if v___x_3021_ == 0 {
                    v___x_3022_ = lean_array_uget_borrowed(v_as_3012_, v_i_3013_);
                    v___x_3023_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3024_ = lean_array_get_size(v___x_3022_);
                    v___x_3025_ = lean_nat_dec_lt(v___x_3023_, v___x_3024_);
                    if v___x_3025_ == 0 {
                        v___y_3017_ = v_b_3015_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3026_ = lean_nat_dec_le(v___x_3024_, v___x_3024_);
                        if v___x_3026_ == 0 {
                            if v___x_3025_ == 0 {
                                v___y_3017_ = v_b_3015_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3027_ = 0usize;
                                v___x_3028_ = lean_usize_of_nat(v___x_3024_);
                                v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v___x_3022_, v___x_3027_, v___x_3028_, v_b_3015_);
                                v___y_3017_ = v___x_3029_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3030_ = 0usize;
                            v___x_3031_ = lean_usize_of_nat(v___x_3024_);
                            v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__0(v___x_3022_, v___x_3030_, v___x_3031_, v_b_3015_);
                            v___y_3017_ = v___x_3032_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_3015_;
                }
            }
            1 => {
                v___x_3018_ = 1usize;
                v___x_3019_ = lean_usize_add(v_i_3013_, v___x_3018_);
                v_i_3013_ = v___x_3019_;
                v_b_3015_ = v___y_3017_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_3033_: *mut crate::leanh::LeanObject,
    mut v_i_3034_: *mut crate::leanh::LeanObject,
    mut v_stop_3035_: *mut crate::leanh::LeanObject,
    mut v_b_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3037_: usize = 0;
    let mut v_stop_boxed_3038_: usize = 0;
    let mut v_res_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3037_ = crate::leanh::lean_unbox_usize(v_i_3034_);
    crate::leanh::lean_dec(v_i_3034_);
    v_stop_boxed_3038_ = crate::leanh::lean_unbox_usize(v_stop_3035_);
    crate::leanh::lean_dec(v_stop_3035_);
    v_res_3039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_as_3033_, v_i_boxed_3037_, v_stop_boxed_3038_, v_b_3036_);
    crate::leanh::lean_dec_ref(v_as_3033_);
    return v_res_3039_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(
    mut v_nss_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    v___x_3041_ = l_Lean_NameSet_empty;
    v___x_3042_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3043_ = lean_array_get_size(v_nss_3040_);
    v___x_3044_ = lean_nat_dec_lt(v___x_3042_, v___x_3043_);
    if v___x_3044_ == 0 {
        return v___x_3041_;
    } else {
        let mut v___x_3045_: u8 = 0;
        v___x_3045_ = lean_nat_dec_le(v___x_3043_, v___x_3043_);
        if v___x_3045_ == 0 {
            if v___x_3044_ == 0 {
                return v___x_3041_;
            } else {
                let mut v___x_3046_: usize = 0;
                let mut v___x_3047_: usize = 0;
                let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3046_ = 0usize;
                v___x_3047_ = lean_usize_of_nat(v___x_3043_);
                v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_nss_3040_, v___x_3046_, v___x_3047_, v___x_3041_);
                return v___x_3048_;
            }
        } else {
            let mut v___x_3049_: usize = 0;
            let mut v___x_3050_: usize = 0;
            let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3049_ = 0usize;
            v___x_3050_ = lean_usize_of_nat(v___x_3043_);
            v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__1(v_nss_3040_, v___x_3049_, v___x_3050_, v___x_3041_);
            return v___x_3051_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(
    mut v_nss_3052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3053_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(v_nss_3052_);
    crate::leanh::lean_dec_ref(v_nss_3052_);
    return v_res_3053_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(
    mut v_hi_3054_: *mut crate::leanh::LeanObject,
    mut v_pivot_3055_: *mut crate::leanh::LeanObject,
    mut v_as_3056_: *mut crate::leanh::LeanObject,
    mut v_i_3057_: *mut crate::leanh::LeanObject,
    mut v_k_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3059_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3059_ = lean_nat_dec_lt(v_k_3058_, v_hi_3054_);
                if v___x_3059_ == 0 {
                    crate::leanh::lean_dec(v_k_3058_);
                    v___x_3060_ = lean_array_fswap(v_as_3056_, v_i_3057_, v_hi_3054_);
                    v___x_3061_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3061_, 0, v_i_3057_);
                    crate::leanh::lean_ctor_set(v___x_3061_, 1, v___x_3060_);
                    return v___x_3061_;
                } else {
                    v___x_3062_ = lean_array_fget_borrowed(v_as_3056_, v_k_3058_);
                    v___x_3063_ = l_Lean_Name_quickLt(v___x_3062_, v_pivot_3055_);
                    if v___x_3063_ == 0 {
                        v___x_3064_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3065_ = lean_nat_add(v_k_3058_, v___x_3064_);
                        crate::leanh::lean_dec(v_k_3058_);
                        v_k_3058_ = v___x_3065_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3067_ = lean_array_fswap(v_as_3056_, v_i_3057_, v_k_3058_);
                        v___x_3068_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3069_ = lean_nat_add(v_i_3057_, v___x_3068_);
                        crate::leanh::lean_dec(v_i_3057_);
                        v___x_3070_ = lean_nat_add(v_k_3058_, v___x_3068_);
                        crate::leanh::lean_dec(v_k_3058_);
                        v_as_3056_ = v___x_3067_;
                        v_i_3057_ = v___x_3069_;
                        v_k_3058_ = v___x_3070_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg___boxed(
    mut v_hi_3072_: *mut crate::leanh::LeanObject,
    mut v_pivot_3073_: *mut crate::leanh::LeanObject,
    mut v_as_3074_: *mut crate::leanh::LeanObject,
    mut v_i_3075_: *mut crate::leanh::LeanObject,
    mut v_k_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(v_hi_3072_, v_pivot_3073_, v_as_3074_, v_i_3075_, v_k_3076_);
    crate::leanh::lean_dec(v_pivot_3073_);
    crate::leanh::lean_dec(v_hi_3072_);
    return v_res_3077_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(
    mut v_n_3078_: *mut crate::leanh::LeanObject,
    mut v_as_3079_: *mut crate::leanh::LeanObject,
    mut v_lo_3080_: *mut crate::leanh::LeanObject,
    mut v_hi_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: u8 = 0;
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3093_ = lean_nat_dec_lt(v_lo_3080_, v_hi_3081_);
                if v___x_3093_ == 0 {
                    crate::leanh::lean_dec(v_lo_3080_);
                    return v_as_3079_;
                } else {
                    v___x_3094_ = lean_nat_add(v_lo_3080_, v_hi_3081_);
                    v___x_3095_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3096_ = lean_nat_shiftr(v___x_3094_, v___x_3095_);
                    crate::leanh::lean_dec(v___x_3094_);
                    v___x_3109_ = lean_array_fget_borrowed(v_as_3079_, v_mid_3096_);
                    v___x_3110_ = lean_array_fget_borrowed(v_as_3079_, v_lo_3080_);
                    v___x_3111_ = l_Lean_Name_quickLt(v___x_3109_, v___x_3110_);
                    if v___x_3111_ == 0 {
                        v___y_3104_ = v_as_3079_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3112_ = lean_array_fswap(v_as_3079_, v_lo_3080_, v_mid_3096_);
                        v___y_3104_ = v___x_3112_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3084_ = lean_array_fget(v___y_3083_, v_hi_3081_);
                crate::leanh::lean_inc_n(v_lo_3080_, 2);
                v___x_3085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(v_hi_3081_, v_pivot_3084_, v___y_3083_, v_lo_3080_, v_lo_3080_);
                crate::leanh::lean_dec(v_pivot_3084_);
                v_fst_3086_ = crate::leanh::lean_ctor_get(v___x_3085_, 0);
                crate::leanh::lean_inc(v_fst_3086_);
                v_snd_3087_ = crate::leanh::lean_ctor_get(v___x_3085_, 1);
                crate::leanh::lean_inc(v_snd_3087_);
                crate::leanh::lean_dec_ref(v___x_3085_);
                v___x_3088_ = lean_nat_dec_le(v_hi_3081_, v_fst_3086_);
                if v___x_3088_ == 0 {
                    v___x_3089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_n_3078_, v_snd_3087_, v_lo_3080_, v_fst_3086_);
                    v___x_3090_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3091_ = lean_nat_add(v_fst_3086_, v___x_3090_);
                    crate::leanh::lean_dec(v_fst_3086_);
                    v_as_3079_ = v___x_3089_;
                    v_lo_3080_ = v___x_3091_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3086_);
                    crate::leanh::lean_dec(v_lo_3080_);
                    return v_snd_3087_;
                }
            }
            2 => {
                v___x_3099_ = lean_array_fget_borrowed(v___y_3098_, v_mid_3096_);
                v___x_3100_ = lean_array_fget_borrowed(v___y_3098_, v_hi_3081_);
                v___x_3101_ = l_Lean_Name_quickLt(v___x_3099_, v___x_3100_);
                if v___x_3101_ == 0 {
                    crate::leanh::lean_dec(v_mid_3096_);
                    v___y_3083_ = v___y_3098_;
                    state = 1;
                    continue;
                } else {
                    v___x_3102_ = lean_array_fswap(v___y_3098_, v_mid_3096_, v_hi_3081_);
                    crate::leanh::lean_dec(v_mid_3096_);
                    v___y_3083_ = v___x_3102_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3105_ = lean_array_fget_borrowed(v___y_3104_, v_hi_3081_);
                v___x_3106_ = lean_array_fget_borrowed(v___y_3104_, v_lo_3080_);
                v___x_3107_ = l_Lean_Name_quickLt(v___x_3105_, v___x_3106_);
                if v___x_3107_ == 0 {
                    v___y_3098_ = v___y_3104_;
                    state = 2;
                    continue;
                } else {
                    v___x_3108_ = lean_array_fswap(v___y_3104_, v_lo_3080_, v_hi_3081_);
                    v___y_3098_ = v___x_3108_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_n_3113_: *mut crate::leanh::LeanObject,
    mut v_as_3114_: *mut crate::leanh::LeanObject,
    mut v_lo_3115_: *mut crate::leanh::LeanObject,
    mut v_hi_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_n_3113_, v_as_3114_, v_lo_3115_, v_hi_3116_);
    crate::leanh::lean_dec(v_hi_3116_);
    crate::leanh::lean_dec(v_n_3113_);
    return v_res_3117_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_(
    mut v_es_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3119_ = lean_array_mk(v_es_3118_);
                v___x_3120_ = lean_array_get_size(v___x_3119_);
                v___x_3121_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3122_ = lean_nat_dec_eq(v___x_3120_, v___x_3121_);
                if v___x_3122_ == 0 {
                    v___x_3123_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3124_ = lean_nat_sub(v___x_3120_, v___x_3123_);
                    v___x_3130_ = lean_nat_dec_le(v___x_3121_, v___x_3124_);
                    if v___x_3130_ == 0 {
                        crate::leanh::lean_inc(v___x_3124_);
                        v___y_3126_ = v___x_3124_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3126_ = v___x_3121_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3119_;
                }
            }
            1 => {
                v___x_3127_ = lean_nat_dec_le(v___y_3126_, v___x_3124_);
                if v___x_3127_ == 0 {
                    crate::leanh::lean_dec(v___x_3124_);
                    crate::leanh::lean_inc(v___y_3126_);
                    v___x_3128_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v___x_3120_, v___x_3119_, v___y_3126_, v___y_3126_);
                    crate::leanh::lean_dec(v___y_3126_);
                    return v___x_3128_;
                } else {
                    v___x_3129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v___x_3120_, v___x_3119_, v___y_3126_, v___x_3124_);
                    crate::leanh::lean_dec(v___x_3124_);
                    return v___x_3129_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_;
    v___x_3148_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3147_);
    return v___x_3148_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2____boxed(
    mut v_a_3149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3150_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
    return v_res_3150_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(
    mut v_n_3151_: *mut crate::leanh::LeanObject,
    mut v_as_3152_: *mut crate::leanh::LeanObject,
    mut v_lo_3153_: *mut crate::leanh::LeanObject,
    mut v_hi_3154_: *mut crate::leanh::LeanObject,
    mut v_w_3155_: *mut crate::leanh::LeanObject,
    mut v_hlo_3156_: *mut crate::leanh::LeanObject,
    mut v_hhi_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___redArg(v_n_3151_, v_as_3152_, v_lo_3153_, v_hi_3154_);
    return v___x_3158_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2___boxed(
    mut v_n_3159_: *mut crate::leanh::LeanObject,
    mut v_as_3160_: *mut crate::leanh::LeanObject,
    mut v_lo_3161_: *mut crate::leanh::LeanObject,
    mut v_hi_3162_: *mut crate::leanh::LeanObject,
    mut v_w_3163_: *mut crate::leanh::LeanObject,
    mut v_hlo_3164_: *mut crate::leanh::LeanObject,
    mut v_hhi_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2(v_n_3159_, v_as_3160_, v_lo_3161_, v_hi_3162_, v_w_3163_, v_hlo_3164_, v_hhi_3165_);
    crate::leanh::lean_dec(v_hi_3162_);
    crate::leanh::lean_dec(v_n_3159_);
    return v_res_3166_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2(
    mut v_n_3167_: *mut crate::leanh::LeanObject,
    mut v_lo_3168_: *mut crate::leanh::LeanObject,
    mut v_hi_3169_: *mut crate::leanh::LeanObject,
    mut v_hhi_3170_: *mut crate::leanh::LeanObject,
    mut v_pivot_3171_: *mut crate::leanh::LeanObject,
    mut v_as_3172_: *mut crate::leanh::LeanObject,
    mut v_i_3173_: *mut crate::leanh::LeanObject,
    mut v_k_3174_: *mut crate::leanh::LeanObject,
    mut v_ilo_3175_: *mut crate::leanh::LeanObject,
    mut v_ik_3176_: *mut crate::leanh::LeanObject,
    mut v_w_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___redArg(v_hi_3169_, v_pivot_3171_, v_as_3172_, v_i_3173_, v_k_3174_);
    return v___x_3178_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2___boxed(
    mut v_n_3179_: *mut crate::leanh::LeanObject,
    mut v_lo_3180_: *mut crate::leanh::LeanObject,
    mut v_hi_3181_: *mut crate::leanh::LeanObject,
    mut v_hhi_3182_: *mut crate::leanh::LeanObject,
    mut v_pivot_3183_: *mut crate::leanh::LeanObject,
    mut v_as_3184_: *mut crate::leanh::LeanObject,
    mut v_i_3185_: *mut crate::leanh::LeanObject,
    mut v_k_3186_: *mut crate::leanh::LeanObject,
    mut v_ilo_3187_: *mut crate::leanh::LeanObject,
    mut v_ik_3188_: *mut crate::leanh::LeanObject,
    mut v_w_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2__spec__2_spec__2(v_n_3179_, v_lo_3180_, v_hi_3181_, v_hhi_3182_, v_pivot_3183_, v_as_3184_, v_i_3185_, v_k_3186_, v_ilo_3187_, v_ik_3188_, v_w_3189_);
    crate::leanh::lean_dec(v_pivot_3183_);
    crate::leanh::lean_dec(v_hi_3181_);
    crate::leanh::lean_dec(v_lo_3180_);
    crate::leanh::lean_dec(v_n_3179_);
    return v_res_3190_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3191_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__0);
    v___x_3193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3192_);
    return v___x_3193_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__1);
    v___x_3195_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3195_, 0, v___x_3194_);
    crate::leanh::lean_ctor_set(v___x_3195_, 1, v___x_3194_);
    return v___x_3195_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(
    mut v_env_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v_unused_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3199_ = lean_st_ref_take(v___y_3197_);
                v_nextMacroScope_3200_ = crate::leanh::lean_ctor_get(v___x_3199_, 1);
                v_ngen_3201_ = crate::leanh::lean_ctor_get(v___x_3199_, 2);
                v_auxDeclNGen_3202_ = crate::leanh::lean_ctor_get(v___x_3199_, 3);
                v_traceState_3203_ = crate::leanh::lean_ctor_get(v___x_3199_, 4);
                v_messages_3204_ = crate::leanh::lean_ctor_get(v___x_3199_, 6);
                v_infoState_3205_ = crate::leanh::lean_ctor_get(v___x_3199_, 7);
                v_snapshotTasks_3206_ = crate::leanh::lean_ctor_get(v___x_3199_, 8);
                v_isSharedCheck_3217_ = (!crate::leanh::lean_is_exclusive(v___x_3199_)) as u8;
                if v_isSharedCheck_3217_ == 0 {
                    v_unused_3218_ = crate::leanh::lean_ctor_get(v___x_3199_, 5);
                    crate::leanh::lean_dec(v_unused_3218_);
                    v_unused_3219_ = crate::leanh::lean_ctor_get(v___x_3199_, 0);
                    crate::leanh::lean_dec(v_unused_3219_);
                    v___x_3208_ = v___x_3199_;
                    v_isShared_3209_ = v_isSharedCheck_3217_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3206_);
                    crate::leanh::lean_inc(v_infoState_3205_);
                    crate::leanh::lean_inc(v_messages_3204_);
                    crate::leanh::lean_inc(v_traceState_3203_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3202_);
                    crate::leanh::lean_inc(v_ngen_3201_);
                    crate::leanh::lean_inc(v_nextMacroScope_3200_);
                    crate::leanh::lean_dec(v___x_3199_);
                    v___x_3208_ = crate::leanh::lean_box(0);
                    v_isShared_3209_ = v_isSharedCheck_3217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3210_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2_once), _init_l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___closed__2);
                if v_isShared_3209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3208_, 5, v___x_3210_);
                    crate::leanh::lean_ctor_set(v___x_3208_, 0, v_env_3196_);
                    v___x_3212_ = v___x_3208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3216_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_env_3196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_nextMacroScope_3200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_ngen_3201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_auxDeclNGen_3202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_traceState_3203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 5, v___x_3210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 6, v_messages_3204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 7, v_infoState_3205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 8, v_snapshotTasks_3206_);
                    v___x_3212_ = v_reuseFailAlloc_3216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3213_ = lean_st_ref_set(v___y_3197_, v___x_3212_);
                v___x_3214_ = crate::leanh::lean_box(0);
                v___x_3215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3214_);
                return v___x_3215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_env_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v_env_3220_, v___y_3221_);
    crate::leanh::lean_dec(v___y_3221_);
    return v_res_3223_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(
    mut v_env_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3228_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v_env_3224_, v___y_3226_);
    return v___x_3228_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3233_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1(v_env_3229_, v___y_3230_, v___y_3231_);
    crate::leanh::lean_dec(v___y_3231_);
    crate::leanh::lean_dec_ref(v___y_3230_);
    return v_res_3233_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3234_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3235_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_3236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3236_, 0, v___x_3235_);
    return v___x_3236_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3237_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_3238_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3239_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3239_, 0, v___x_3238_);
    crate::leanh::lean_ctor_set(v___x_3239_, 1, v___x_3238_);
    crate::leanh::lean_ctor_set(v___x_3239_, 2, v___x_3238_);
    crate::leanh::lean_ctor_set(v___x_3239_, 3, v___x_3238_);
    crate::leanh::lean_ctor_set(v___x_3239_, 4, v___x_3237_);
    crate::leanh::lean_ctor_set(v___x_3239_, 5, v___x_3237_);
    crate::leanh::lean_ctor_set(v___x_3239_, 6, v___x_3237_);
    crate::leanh::lean_ctor_set(v___x_3239_, 7, v___x_3237_);
    crate::leanh::lean_ctor_set(v___x_3239_, 8, v___x_3237_);
    crate::leanh::lean_ctor_set(v___x_3239_, 9, v___x_3237_);
    return v___x_3239_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3240_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3241_ = lean_mk_empty_array_with_capacity(v___x_3240_);
    v___x_3242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3242_, 0, v___x_3241_);
    return v___x_3242_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3243_: usize = 0;
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = 5usize;
    v___x_3244_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3245_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3246_ = lean_mk_empty_array_with_capacity(v___x_3245_);
    v___x_3247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_3248_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3248_, 0, v___x_3247_);
    crate::leanh::lean_ctor_set(v___x_3248_, 1, v___x_3246_);
    crate::leanh::lean_ctor_set(v___x_3248_, 2, v___x_3244_);
    crate::leanh::lean_ctor_set(v___x_3248_, 3, v___x_3244_);
    crate::leanh::lean_ctor_set_usize(v___x_3248_, 4, v___x_3243_);
    return v___x_3248_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3249_ = crate::leanh::lean_box(1);
    v___x_3250_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_3251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_3252_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3252_, 0, v___x_3251_);
    crate::leanh::lean_ctor_set(v___x_3252_, 1, v___x_3250_);
    crate::leanh::lean_ctor_set(v___x_3252_, 2, v___x_3249_);
    return v___x_3252_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = lean_st_ref_get(v___y_3255_);
    v_env_3258_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
    crate::leanh::lean_inc_ref(v_env_3258_);
    crate::leanh::lean_dec(v___x_3257_);
    v_options_3259_ = crate::leanh::lean_ctor_get(v___y_3254_, 2);
    v___x_3260_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_3261_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_3259_);
    v___x_3262_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3262_, 0, v_env_3258_);
    crate::leanh::lean_ctor_set(v___x_3262_, 1, v___x_3260_);
    crate::leanh::lean_ctor_set(v___x_3262_, 2, v___x_3261_);
    crate::leanh::lean_ctor_set(v___x_3262_, 3, v_options_3259_);
    v___x_3263_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3263_, 1, v_msgData_3253_);
    v___x_3264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3263_);
    return v___x_3264_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3269_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3265_, v___y_3266_, v___y_3267_);
    crate::leanh::lean_dec(v___y_3267_);
    crate::leanh::lean_dec_ref(v___y_3266_);
    return v_res_3269_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3274_ = crate::leanh::lean_ctor_get(v___y_3271_, 5);
                v___x_3275_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msg_3270_, v___y_3271_, v___y_3272_);
                v_a_3276_ = crate::leanh::lean_ctor_get(v___x_3275_, 0);
                v_isSharedCheck_3284_ = (!crate::leanh::lean_is_exclusive(v___x_3275_)) as u8;
                if v_isSharedCheck_3284_ == 0 {
                    v___x_3278_ = v___x_3275_;
                    v_isShared_3279_ = v_isSharedCheck_3284_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3276_);
                    crate::leanh::lean_dec(v___x_3275_);
                    v___x_3278_ = crate::leanh::lean_box(0);
                    v_isShared_3279_ = v_isSharedCheck_3284_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3274_);
                v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3280_, 0, v_ref_3274_);
                crate::leanh::lean_ctor_set(v___x_3280_, 1, v_a_3276_);
                if v_isShared_3279_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3278_, 1);
                    crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3280_);
                    v___x_3282_ = v___x_3278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
    mut v___y_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_3285_, v___y_3286_, v___y_3287_);
    crate::leanh::lean_dec(v___y_3287_);
    crate::leanh::lean_dec_ref(v___y_3286_);
    return v_res_3289_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3291_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
    v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
    return v___x_3292_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3294_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
    v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
    return v___x_3295_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(
    mut v_name_3296_: *mut crate::leanh::LeanObject,
    mut v_decl_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_);
    v___x_3302_ = l_Lean_MessageData_ofName(v_name_3296_);
    v___x_3303_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3303_, 0, v___x_3301_);
    crate::leanh::lean_ctor_set(v___x_3303_, 1, v___x_3302_);
    v___x_3304_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_);
    v___x_3305_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3305_, 0, v___x_3303_);
    crate::leanh::lean_ctor_set(v___x_3305_, 1, v___x_3304_);
    v___x_3306_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_3305_, v___y_3298_, v___y_3299_);
    return v___x_3306_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(
    mut v_name_3307_: *mut crate::leanh::LeanObject,
    mut v_decl_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3312_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_name_3307_, v_decl_3308_, v___y_3309_, v___y_3310_);
    crate::leanh::lean_dec(v___y_3310_);
    crate::leanh::lean_dec_ref(v___y_3309_);
    crate::leanh::lean_dec(v_decl_3308_);
    return v_res_3312_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__0;
    v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
    return v___x_3315_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__2;
    v___x_3318_ = l_Lean_stringToMessageData(v___x_3317_);
    return v___x_3318_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__4;
    v___x_3321_ = l_Lean_stringToMessageData(v___x_3320_);
    return v___x_3321_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(
    mut v_name_3325_: *mut crate::leanh::LeanObject,
    mut v_kind_3326_: u8,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3330_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__1);
                v___x_3331_ = l_Lean_MessageData_ofName(v_name_3325_);
                v___x_3332_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3330_);
                crate::leanh::lean_ctor_set(v___x_3332_, 1, v___x_3331_);
                v___x_3333_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__3);
                v___x_3334_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3334_, 0, v___x_3332_);
                crate::leanh::lean_ctor_set(v___x_3334_, 1, v___x_3333_);
                match v_kind_3326_ {
                    0 => {
                        v___x_3343_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__6;
                        v___y_3336_ = v___x_3343_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_3344_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__7;
                        v___y_3336_ = v___x_3344_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_3345_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__8;
                        v___y_3336_ = v___x_3345_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_3336_);
                v___x_3337_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3337_, 0, v___y_3336_);
                v___x_3338_ = l_Lean_MessageData_ofFormat(v___x_3337_);
                v___x_3339_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3339_, 0, v___x_3334_);
                crate::leanh::lean_ctor_set(v___x_3339_, 1, v___x_3338_);
                v___x_3340_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5);
                v___x_3341_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3341_, 0, v___x_3339_);
                crate::leanh::lean_ctor_set(v___x_3341_, 1, v___x_3340_);
                v___x_3342_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_3341_, v___y_3327_, v___y_3328_);
                return v___x_3342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___boxed(
    mut v_name_3346_: *mut crate::leanh::LeanObject,
    mut v_kind_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3351_: u8 = 0;
    let mut v_res_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3351_ = (crate::leanh::lean_unbox(v_kind_3347_) as u8);
    v_res_3352_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_3346_, v_kind_boxed_3351_, v___y_3348_, v___y_3349_);
    crate::leanh::lean_dec(v___y_3349_);
    crate::leanh::lean_dec_ref(v___y_3348_);
    return v_res_3352_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__0;
    v___x_3355_ = l_Lean_stringToMessageData(v___x_3354_);
    return v___x_3355_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__2;
    v___x_3358_ = l_Lean_stringToMessageData(v___x_3357_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__4;
    v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
    return v___x_3361_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3363_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__6;
    v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
    return v___x_3364_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__8;
    v___x_3367_ = l_Lean_stringToMessageData(v___x_3366_);
    return v___x_3367_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(
    mut v_attrName_3368_: *mut crate::leanh::LeanObject,
    mut v_declName_3369_: *mut crate::leanh::LeanObject,
    mut v_givenType_3370_: *mut crate::leanh::LeanObject,
    mut v_expectedType_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: u8 = 0;
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3375_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__1);
    v___x_3376_ = l_Lean_MessageData_ofName(v_attrName_3368_);
    crate::leanh::lean_inc_ref(v___x_3376_);
    v___x_3377_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3375_);
    crate::leanh::lean_ctor_set(v___x_3377_, 1, v___x_3376_);
    v___x_3378_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__3);
    v___x_3379_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3379_, 0, v___x_3377_);
    crate::leanh::lean_ctor_set(v___x_3379_, 1, v___x_3378_);
    v___x_3380_ = 0;
    v___x_3381_ = l_Lean_MessageData_ofConstName(v_declName_3369_, v___x_3380_);
    v___x_3382_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3382_, 0, v___x_3379_);
    crate::leanh::lean_ctor_set(v___x_3382_, 1, v___x_3381_);
    v___x_3383_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__5);
    v___x_3384_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3384_, 0, v___x_3382_);
    crate::leanh::lean_ctor_set(v___x_3384_, 1, v___x_3383_);
    v___x_3385_ = l_Lean_indentExpr(v_givenType_3370_);
    v___x_3386_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3386_, 0, v___x_3384_);
    crate::leanh::lean_ctor_set(v___x_3386_, 1, v___x_3385_);
    v___x_3387_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__7);
    v___x_3388_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3388_, 0, v___x_3386_);
    crate::leanh::lean_ctor_set(v___x_3388_, 1, v___x_3387_);
    v___x_3389_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3389_, 0, v___x_3388_);
    crate::leanh::lean_ctor_set(v___x_3389_, 1, v___x_3376_);
    v___x_3390_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___closed__9);
    v___x_3391_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3391_, 0, v___x_3389_);
    crate::leanh::lean_ctor_set(v___x_3391_, 1, v___x_3390_);
    v___x_3392_ = l_Lean_indentExpr(v_expectedType_3371_);
    v___x_3393_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3393_, 0, v___x_3391_);
    crate::leanh::lean_ctor_set(v___x_3393_, 1, v___x_3392_);
    v___x_3394_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v___x_3393_, v___y_3372_, v___y_3373_);
    return v___x_3394_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg___boxed(
    mut v_attrName_3395_: *mut crate::leanh::LeanObject,
    mut v_declName_3396_: *mut crate::leanh::LeanObject,
    mut v_givenType_3397_: *mut crate::leanh::LeanObject,
    mut v_expectedType_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3402_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_attrName_3395_, v_declName_3396_, v_givenType_3397_, v_expectedType_3398_, v___y_3399_, v___y_3400_);
    crate::leanh::lean_dec(v___y_3400_);
    crate::leanh::lean_dec_ref(v___y_3399_);
    return v_res_3402_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(
    mut v_ref_3403_: *mut crate::leanh::LeanObject,
    mut v_msg_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3420_: u8 = 0;
    let mut v_cancelTk_x3f_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3422_: u8 = 0;
    let mut v_inheritedTraceOptions_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3408_ = crate::leanh::lean_ctor_get(v___y_3405_, 0);
    v_fileMap_3409_ = crate::leanh::lean_ctor_get(v___y_3405_, 1);
    v_options_3410_ = crate::leanh::lean_ctor_get(v___y_3405_, 2);
    v_currRecDepth_3411_ = crate::leanh::lean_ctor_get(v___y_3405_, 3);
    v_maxRecDepth_3412_ = crate::leanh::lean_ctor_get(v___y_3405_, 4);
    v_ref_3413_ = crate::leanh::lean_ctor_get(v___y_3405_, 5);
    v_currNamespace_3414_ = crate::leanh::lean_ctor_get(v___y_3405_, 6);
    v_openDecls_3415_ = crate::leanh::lean_ctor_get(v___y_3405_, 7);
    v_initHeartbeats_3416_ = crate::leanh::lean_ctor_get(v___y_3405_, 8);
    v_maxHeartbeats_3417_ = crate::leanh::lean_ctor_get(v___y_3405_, 9);
    v_quotContext_3418_ = crate::leanh::lean_ctor_get(v___y_3405_, 10);
    v_currMacroScope_3419_ = crate::leanh::lean_ctor_get(v___y_3405_, 11);
    v_diag_3420_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3405_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3421_ = crate::leanh::lean_ctor_get(v___y_3405_, 12);
    v_suppressElabErrors_3422_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3405_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3423_ = crate::leanh::lean_ctor_get(v___y_3405_, 13);
    v_ref_3424_ = l_Lean_replaceRef(v_ref_3403_, v_ref_3413_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3423_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3421_);
    crate::leanh::lean_inc(v_currMacroScope_3419_);
    crate::leanh::lean_inc(v_quotContext_3418_);
    crate::leanh::lean_inc(v_maxHeartbeats_3417_);
    crate::leanh::lean_inc(v_initHeartbeats_3416_);
    crate::leanh::lean_inc(v_openDecls_3415_);
    crate::leanh::lean_inc(v_currNamespace_3414_);
    crate::leanh::lean_inc(v_maxRecDepth_3412_);
    crate::leanh::lean_inc(v_currRecDepth_3411_);
    crate::leanh::lean_inc_ref(v_options_3410_);
    crate::leanh::lean_inc_ref(v_fileMap_3409_);
    crate::leanh::lean_inc_ref(v_fileName_3408_);
    v___x_3425_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3425_, 0, v_fileName_3408_);
    crate::leanh::lean_ctor_set(v___x_3425_, 1, v_fileMap_3409_);
    crate::leanh::lean_ctor_set(v___x_3425_, 2, v_options_3410_);
    crate::leanh::lean_ctor_set(v___x_3425_, 3, v_currRecDepth_3411_);
    crate::leanh::lean_ctor_set(v___x_3425_, 4, v_maxRecDepth_3412_);
    crate::leanh::lean_ctor_set(v___x_3425_, 5, v_ref_3424_);
    crate::leanh::lean_ctor_set(v___x_3425_, 6, v_currNamespace_3414_);
    crate::leanh::lean_ctor_set(v___x_3425_, 7, v_openDecls_3415_);
    crate::leanh::lean_ctor_set(v___x_3425_, 8, v_initHeartbeats_3416_);
    crate::leanh::lean_ctor_set(v___x_3425_, 9, v_maxHeartbeats_3417_);
    crate::leanh::lean_ctor_set(v___x_3425_, 10, v_quotContext_3418_);
    crate::leanh::lean_ctor_set(v___x_3425_, 11, v_currMacroScope_3419_);
    crate::leanh::lean_ctor_set(v___x_3425_, 12, v_cancelTk_x3f_3421_);
    crate::leanh::lean_ctor_set(v___x_3425_, 13, v_inheritedTraceOptions_3423_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3425_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3420_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3425_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3422_,
    );
    v___x_3426_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_3404_, v___x_3425_, v___y_3406_);
    crate::leanh::lean_dec_ref_known(v___x_3425_, 14);
    return v___x_3426_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(
    mut v_ref_3427_: *mut crate::leanh::LeanObject,
    mut v_msg_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3427_, v_msg_3428_, v___y_3429_, v___y_3430_);
    crate::leanh::lean_dec(v___y_3430_);
    crate::leanh::lean_dec_ref(v___y_3429_);
    crate::leanh::lean_dec(v_ref_3427_);
    return v_res_3432_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0;
    v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2;
    v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4;
    v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
    return v___x_3441_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_3444_ = l_Lean_stringToMessageData(v___x_3443_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3446_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_3447_ = l_Lean_stringToMessageData(v___x_3446_);
    return v___x_3447_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3449_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_3450_ = l_Lean_stringToMessageData(v___x_3449_);
    return v___x_3450_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_3453_ = l_Lean_stringToMessageData(v___x_3452_);
    return v___x_3453_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(
    mut v_msg_3454_: *mut crate::leanh::LeanObject,
    mut v_declHint_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: u8 = 0;
    let mut v_isExporting_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: u8 = 0;
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3515_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3458_ = lean_st_ref_get(v___y_3456_);
                v_env_3459_ = crate::leanh::lean_ctor_get(v___x_3458_, 0);
                crate::leanh::lean_inc_ref(v_env_3459_);
                crate::leanh::lean_dec(v___x_3458_);
                v___x_3460_ = l_Lean_Name_isAnonymous(v_declHint_3455_);
                if v___x_3460_ == 0 {
                    v_isExporting_3461_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3459_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3461_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3459_);
                        crate::leanh::lean_dec(v_declHint_3455_);
                        v___x_3462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3462_, 0, v_msg_3454_);
                        return v___x_3462_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3459_);
                        v___x_3463_ = l_Lean_Environment_setExporting(v_env_3459_, v___x_3460_);
                        crate::leanh::lean_inc(v_declHint_3455_);
                        crate::leanh::lean_inc_ref(v___x_3463_);
                        v___x_3464_ = l_Lean_Environment_contains(
                            v___x_3463_,
                            v_declHint_3455_,
                            v_isExporting_3461_,
                        );
                        if v___x_3464_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3463_);
                            crate::leanh::lean_dec_ref(v_env_3459_);
                            crate::leanh::lean_dec(v_declHint_3455_);
                            v___x_3465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3465_, 0, v_msg_3454_);
                            return v___x_3465_;
                        } else {
                            v___x_3466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__2);
                            v___x_3467_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0___closed__5);
                            v___x_3468_ = l_Lean_Options_empty;
                            v___x_3469_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3463_);
                            crate::leanh::lean_ctor_set(v___x_3469_, 1, v___x_3466_);
                            crate::leanh::lean_ctor_set(v___x_3469_, 2, v___x_3467_);
                            crate::leanh::lean_ctor_set(v___x_3469_, 3, v___x_3468_);
                            crate::leanh::lean_inc(v_declHint_3455_);
                            v___x_3470_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3455_, v___x_3460_);
                            v_c_3471_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3471_, 0, v___x_3469_);
                            crate::leanh::lean_ctor_set(v_c_3471_, 1, v___x_3470_);
                            v___x_3472_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3459_,
                                v_declHint_3455_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3472_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3459_);
                                crate::leanh::lean_dec(v_declHint_3455_);
                                v___x_3473_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
                                v___x_3474_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3474_, 0, v___x_3473_);
                                crate::leanh::lean_ctor_set(v___x_3474_, 1, v_c_3471_);
                                v___x_3475_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
                                v___x_3476_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3476_, 0, v___x_3474_);
                                crate::leanh::lean_ctor_set(v___x_3476_, 1, v___x_3475_);
                                v___x_3477_ = l_Lean_MessageData_note(v___x_3476_);
                                v___x_3478_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3478_, 0, v_msg_3454_);
                                crate::leanh::lean_ctor_set(v___x_3478_, 1, v___x_3477_);
                                v___x_3479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3479_, 0, v___x_3478_);
                                return v___x_3479_;
                            } else {
                                v_val_3480_ = crate::leanh::lean_ctor_get(v___x_3472_, 0);
                                v_isSharedCheck_3515_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3472_)) as u8;
                                if v_isSharedCheck_3515_ == 0 {
                                    v___x_3482_ = v___x_3472_;
                                    v_isShared_3483_ = v_isSharedCheck_3515_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3480_);
                                    crate::leanh::lean_dec(v___x_3472_);
                                    v___x_3482_ = crate::leanh::lean_box(0);
                                    v_isShared_3483_ = v_isSharedCheck_3515_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3459_);
                    crate::leanh::lean_dec(v_declHint_3455_);
                    v___x_3516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3516_, 0, v_msg_3454_);
                    return v___x_3516_;
                }
            }
            1 => {
                v___x_3484_ = crate::leanh::lean_box(0);
                v___x_3485_ = l_Lean_Environment_header(v_env_3459_);
                crate::leanh::lean_dec_ref(v_env_3459_);
                v___x_3486_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3485_);
                v_mod_3487_ = lean_array_get(v___x_3484_, v___x_3486_, v_val_3480_);
                crate::leanh::lean_dec(v_val_3480_);
                crate::leanh::lean_dec_ref(v___x_3486_);
                v___x_3488_ = l_Lean_isPrivateName(v_declHint_3455_);
                crate::leanh::lean_dec(v_declHint_3455_);
                if v___x_3488_ == 0 {
                    v___x_3489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
                    v___x_3490_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3490_, 0, v___x_3489_);
                    crate::leanh::lean_ctor_set(v___x_3490_, 1, v_c_3471_);
                    v___x_3491_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_3492_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3490_);
                    crate::leanh::lean_ctor_set(v___x_3492_, 1, v___x_3491_);
                    v___x_3493_ = l_Lean_MessageData_ofName(v_mod_3487_);
                    v___x_3494_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3494_, 0, v___x_3492_);
                    crate::leanh::lean_ctor_set(v___x_3494_, 1, v___x_3493_);
                    v___x_3495_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
                    v___x_3496_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3496_, 0, v___x_3494_);
                    crate::leanh::lean_ctor_set(v___x_3496_, 1, v___x_3495_);
                    v___x_3497_ = l_Lean_MessageData_note(v___x_3496_);
                    v___x_3498_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3498_, 0, v_msg_3454_);
                    crate::leanh::lean_ctor_set(v___x_3498_, 1, v___x_3497_);
                    if v_isShared_3483_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3482_, 0);
                        crate::leanh::lean_ctor_set(v___x_3482_, 0, v___x_3498_);
                        v___x_3500_ = v___x_3482_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
                        v___x_3500_ = v_reuseFailAlloc_3501_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3502_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
                    v___x_3503_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3503_, 0, v___x_3502_);
                    crate::leanh::lean_ctor_set(v___x_3503_, 1, v_c_3471_);
                    v___x_3504_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_3505_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3505_, 0, v___x_3503_);
                    crate::leanh::lean_ctor_set(v___x_3505_, 1, v___x_3504_);
                    v___x_3506_ = l_Lean_MessageData_ofName(v_mod_3487_);
                    v___x_3507_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3507_, 0, v___x_3505_);
                    crate::leanh::lean_ctor_set(v___x_3507_, 1, v___x_3506_);
                    v___x_3508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_3509_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3509_, 0, v___x_3507_);
                    crate::leanh::lean_ctor_set(v___x_3509_, 1, v___x_3508_);
                    v___x_3510_ = l_Lean_MessageData_note(v___x_3509_);
                    v___x_3511_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3511_, 0, v_msg_3454_);
                    crate::leanh::lean_ctor_set(v___x_3511_, 1, v___x_3510_);
                    if v_isShared_3483_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3482_, 0);
                        crate::leanh::lean_ctor_set(v___x_3482_, 0, v___x_3511_);
                        v___x_3513_ = v___x_3482_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
                        v___x_3513_ = v_reuseFailAlloc_3514_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3500_;
            }
            3 => {
                return v___x_3513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_3517_: *mut crate::leanh::LeanObject,
    mut v_declHint_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3517_, v_declHint_3518_, v___y_3519_);
    crate::leanh::lean_dec(v___y_3519_);
    return v_res_3521_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(
    mut v_msg_3522_: *mut crate::leanh::LeanObject,
    mut v_declHint_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
    mut v___y_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3527_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3522_, v_declHint_3523_, v___y_3525_);
                v_a_3528_ = crate::leanh::lean_ctor_get(v___x_3527_, 0);
                v_isSharedCheck_3537_ = (!crate::leanh::lean_is_exclusive(v___x_3527_)) as u8;
                if v_isSharedCheck_3537_ == 0 {
                    v___x_3530_ = v___x_3527_;
                    v_isShared_3531_ = v_isSharedCheck_3537_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3528_);
                    crate::leanh::lean_dec(v___x_3527_);
                    v___x_3530_ = crate::leanh::lean_box(0);
                    v_isShared_3531_ = v_isSharedCheck_3537_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3532_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3533_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3533_, 0, v___x_3532_);
                crate::leanh::lean_ctor_set(v___x_3533_, 1, v_a_3528_);
                if v_isShared_3531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3530_, 0, v___x_3533_);
                    v___x_3535_ = v___x_3530_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
                    v___x_3535_ = v_reuseFailAlloc_3536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(
    mut v_msg_3538_: *mut crate::leanh::LeanObject,
    mut v_declHint_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3543_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_3538_, v_declHint_3539_, v___y_3540_, v___y_3541_);
    crate::leanh::lean_dec(v___y_3541_);
    crate::leanh::lean_dec_ref(v___y_3540_);
    return v_res_3543_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(
    mut v_ref_3544_: *mut crate::leanh::LeanObject,
    mut v_msg_3545_: *mut crate::leanh::LeanObject,
    mut v_declHint_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_3545_, v_declHint_3546_, v___y_3547_, v___y_3548_);
    v_a_3551_ = crate::leanh::lean_ctor_get(v___x_3550_, 0);
    crate::leanh::lean_inc(v_a_3551_);
    crate::leanh::lean_dec_ref(v___x_3550_);
    v___x_3552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3544_, v_a_3551_, v___y_3547_, v___y_3548_);
    return v___x_3552_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_ref_3553_: *mut crate::leanh::LeanObject,
    mut v_msg_3554_: *mut crate::leanh::LeanObject,
    mut v_declHint_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3553_, v_msg_3554_, v_declHint_3555_, v___y_3556_, v___y_3557_);
    crate::leanh::lean_dec(v___y_3557_);
    crate::leanh::lean_dec_ref(v___y_3556_);
    crate::leanh::lean_dec(v_ref_3553_);
    return v_res_3559_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_3562_ = l_Lean_stringToMessageData(v___x_3561_);
    return v___x_3562_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(
    mut v_ref_3563_: *mut crate::leanh::LeanObject,
    mut v_constName_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3569_ = 0;
    crate::leanh::lean_inc(v_constName_3564_);
    v___x_3570_ = l_Lean_MessageData_ofConstName(v_constName_3564_, v___x_3569_);
    v___x_3571_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3571_, 0, v___x_3568_);
    crate::leanh::lean_ctor_set(v___x_3571_, 1, v___x_3570_);
    v___x_3572_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg___closed__5);
    v___x_3573_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3573_, 0, v___x_3571_);
    crate::leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    v___x_3574_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3563_, v___x_3573_, v_constName_3564_, v___y_3565_, v___y_3566_);
    return v___x_3574_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(
    mut v_ref_3575_: *mut crate::leanh::LeanObject,
    mut v_constName_3576_: *mut crate::leanh::LeanObject,
    mut v___y_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3580_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_3575_, v_constName_3576_, v___y_3577_, v___y_3578_);
    crate::leanh::lean_dec(v___y_3578_);
    crate::leanh::lean_dec_ref(v___y_3577_);
    crate::leanh::lean_dec(v_ref_3575_);
    return v_res_3580_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_constName_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3585_ = crate::leanh::lean_ctor_get(v___y_3582_, 5);
    v___x_3586_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_3585_, v_constName_3581_, v___y_3582_, v___y_3583_);
    return v___x_3586_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(
    mut v_constName_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_3587_, v___y_3588_, v___y_3589_);
    crate::leanh::lean_dec(v___y_3589_);
    crate::leanh::lean_dec_ref(v___y_3588_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(
    mut v_constName_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3596_ = lean_st_ref_get(v___y_3594_);
                v_env_3597_ = crate::leanh::lean_ctor_get(v___x_3596_, 0);
                crate::leanh::lean_inc_ref(v_env_3597_);
                crate::leanh::lean_dec(v___x_3596_);
                v___x_3598_ = 0;
                crate::leanh::lean_inc(v_constName_3592_);
                v___x_3599_ =
                    l_Lean_Environment_find_x3f(v_env_3597_, v_constName_3592_, v___x_3598_);
                if crate::leanh::lean_obj_tag(v___x_3599_) == 0 {
                    v___x_3600_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_3592_, v___y_3593_, v___y_3594_);
                    return v___x_3600_;
                } else {
                    crate::leanh::lean_dec(v_constName_3592_);
                    v_val_3601_ = crate::leanh::lean_ctor_get(v___x_3599_, 0);
                    v_isSharedCheck_3608_ = (!crate::leanh::lean_is_exclusive(v___x_3599_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3603_ = v___x_3599_;
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3601_);
                        crate::leanh::lean_dec(v___x_3599_);
                        v___x_3603_ = crate::leanh::lean_box(0);
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3604_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3603_, 0);
                    v___x_3606_ = v___x_3603_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_val_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2___boxed(
    mut v_constName_3609_: *mut crate::leanh::LeanObject,
    mut v___y_3610_: *mut crate::leanh::LeanObject,
    mut v___y_3611_: *mut crate::leanh::LeanObject,
    mut v___y_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(v_constName_3609_, v___y_3610_, v___y_3611_);
    crate::leanh::lean_dec(v___y_3611_);
    crate::leanh::lean_dec_ref(v___y_3610_);
    return v_res_3613_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(
    mut v_builtin_3619_: u8,
    mut v___x_3620_: *mut crate::leanh::LeanObject,
    mut v___x_3621_: *mut crate::leanh::LeanObject,
    mut v___x_3622_: *mut crate::leanh::LeanObject,
    mut v_name_3623_: *mut crate::leanh::LeanObject,
    mut v_decl_3624_: *mut crate::leanh::LeanObject,
    mut v_stx_3625_: *mut crate::leanh::LeanObject,
    mut v_kind_3626_: u8,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: u8 = 0;
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_builtin_3619_ == 0 {
                    v___x_3673_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
                    crate::leanh::lean_inc(v_decl_3624_);
                    v___x_3674_ = l_Lean_ensureAttrDeclIsMeta(
                        v___x_3673_,
                        v_decl_3624_,
                        v_kind_3626_,
                        v___y_3627_,
                        v___y_3628_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3674_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3674_, 1);
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_stx_3625_);
                        crate::leanh::lean_dec(v_decl_3624_);
                        crate::leanh::lean_dec(v_name_3623_);
                        crate::leanh::lean_dec_ref(v___x_3622_);
                        crate::leanh::lean_dec_ref(v___x_3621_);
                        crate::leanh::lean_dec(v___x_3620_);
                        return v___x_3674_;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_3633_ = lean_st_ref_get(v___y_3632_);
                if v_builtin_3619_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3622_);
                    crate::leanh::lean_dec_ref(v___x_3621_);
                    v_env_3634_ = crate::leanh::lean_ctor_get(v___x_3633_, 0);
                    crate::leanh::lean_inc_ref(v_env_3634_);
                    crate::leanh::lean_dec(v___x_3633_);
                    v___x_3635_ = l_Lean_Server_codeActionProviderExt;
                    v_toEnvExtension_3636_ = crate::leanh::lean_ctor_get(v___x_3635_, 0);
                    v_asyncMode_3637_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3636_, 2);
                    v___x_3638_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                        v___x_3635_,
                        v_env_3634_,
                        v_decl_3624_,
                        v_asyncMode_3637_,
                        v___x_3620_,
                    );
                    v___x_3639_ = l_Lean_setEnv___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__1___redArg(v___x_3638_, v___y_3632_);
                    return v___x_3639_;
                } else {
                    crate::leanh::lean_dec(v___x_3633_);
                    crate::leanh::lean_dec(v___x_3620_);
                    v___x_3640_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_n(v_decl_3624_, 2);
                    v___x_3641_ = l_Lean_mkConst(v_decl_3624_, v___x_3640_);
                    v___x_3642_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
                    v___x_3643_ = l_Lean_Name_mkStr3(v___x_3621_, v___x_3622_, v___x_3642_);
                    v___x_3644_ = l_Lean_mkConst(v___x_3643_, v___x_3640_);
                    v___x_3645_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_3624_);
                    v___x_3646_ = l_Lean_mkAppB(v___x_3644_, v___x_3645_, v___x_3641_);
                    v___x_3647_ =
                        l_Lean_declareBuiltin(v_decl_3624_, v___x_3646_, v___y_3631_, v___y_3632_);
                    return v___x_3647_;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_decl_3624_);
                v___x_3651_ = l_Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2(v_decl_3624_, v___y_3649_, v___y_3650_);
                if crate::leanh::lean_obj_tag(v___x_3651_) == 0 {
                    v_a_3652_ = crate::leanh::lean_ctor_get(v___x_3651_, 0);
                    crate::leanh::lean_inc(v_a_3652_);
                    crate::leanh::lean_dec_ref_known(v___x_3651_, 1);
                    v___x_3653_ = l_Lean_ConstantInfo_type(v_a_3652_);
                    crate::leanh::lean_dec(v_a_3652_);
                    v___x_3654_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___x_3622_);
                    crate::leanh::lean_inc_ref(v___x_3621_);
                    v___x_3655_ = l_Lean_Name_mkStr3(v___x_3621_, v___x_3622_, v___x_3654_);
                    v___x_3656_ = l_Lean_Expr_isConstOf(v___x_3653_, v___x_3655_);
                    if v___x_3656_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3622_);
                        crate::leanh::lean_dec_ref(v___x_3621_);
                        crate::leanh::lean_dec(v___x_3620_);
                        v___x_3657_ = crate::leanh::lean_box(0);
                        v___x_3658_ = l_Lean_mkConst(v___x_3655_, v___x_3657_);
                        v___x_3659_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_name_3623_, v_decl_3624_, v___x_3653_, v___x_3658_, v___y_3649_, v___y_3650_);
                        return v___x_3659_;
                    } else {
                        crate::leanh::lean_dec(v___x_3655_);
                        crate::leanh::lean_dec_ref(v___x_3653_);
                        crate::leanh::lean_dec(v_name_3623_);
                        v___y_3631_ = v___y_3649_;
                        v___y_3632_ = v___y_3650_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_decl_3624_);
                    crate::leanh::lean_dec(v_name_3623_);
                    crate::leanh::lean_dec_ref(v___x_3622_);
                    crate::leanh::lean_dec_ref(v___x_3621_);
                    crate::leanh::lean_dec(v___x_3620_);
                    v_a_3660_ = crate::leanh::lean_ctor_get(v___x_3651_, 0);
                    v_isSharedCheck_3667_ = (!crate::leanh::lean_is_exclusive(v___x_3651_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3662_ = v___x_3651_;
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3660_);
                        crate::leanh::lean_dec(v___x_3651_);
                        v___x_3662_ = crate::leanh::lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3663_ == 0 {
                    v___x_3665_ = v___x_3662_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
                    v___x_3665_ = v_reuseFailAlloc_3666_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3665_;
            }
            5 => {
                v___x_3669_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3625_, v___y_3627_, v___y_3628_);
                if crate::leanh::lean_obj_tag(v___x_3669_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3669_, 1);
                    v___x_3670_ = 0;
                    v___x_3671_ = l_Lean_instBEqAttributeKind_beq(v_kind_3626_, v___x_3670_);
                    if v___x_3671_ == 0 {
                        crate::leanh::lean_dec(v_decl_3624_);
                        crate::leanh::lean_dec_ref(v___x_3622_);
                        crate::leanh::lean_dec_ref(v___x_3621_);
                        crate::leanh::lean_dec(v___x_3620_);
                        v___x_3672_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_3623_, v_kind_3626_, v___y_3627_, v___y_3628_);
                        return v___x_3672_;
                    } else {
                        v___y_3649_ = v___y_3627_;
                        v___y_3650_ = v___y_3628_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_decl_3624_);
                    crate::leanh::lean_dec(v_name_3623_);
                    crate::leanh::lean_dec_ref(v___x_3622_);
                    crate::leanh::lean_dec_ref(v___x_3621_);
                    crate::leanh::lean_dec(v___x_3620_);
                    return v___x_3669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(
    mut v_builtin_3675_: *mut crate::leanh::LeanObject,
    mut v___x_3676_: *mut crate::leanh::LeanObject,
    mut v___x_3677_: *mut crate::leanh::LeanObject,
    mut v___x_3678_: *mut crate::leanh::LeanObject,
    mut v_name_3679_: *mut crate::leanh::LeanObject,
    mut v_decl_3680_: *mut crate::leanh::LeanObject,
    mut v_stx_3681_: *mut crate::leanh::LeanObject,
    mut v_kind_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_builtin_boxed_3686_: u8 = 0;
    let mut v_kind_boxed_3687_: u8 = 0;
    let mut v_res_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3686_ = (crate::leanh::lean_unbox(v_builtin_3675_) as u8);
    v_kind_boxed_3687_ = (crate::leanh::lean_unbox(v_kind_3682_) as u8);
    v_res_3688_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_builtin_boxed_3686_, v___x_3676_, v___x_3677_, v___x_3678_, v_name_3679_, v_decl_3680_, v_stx_3681_, v_kind_boxed_3687_, v___y_3683_, v___y_3684_);
    crate::leanh::lean_dec(v___y_3684_);
    crate::leanh::lean_dec_ref(v___y_3683_);
    return v_res_3688_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(
    mut v_builtin_3752_: u8,
    mut v_name_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_n(v_name_3753_, 2);
                v___f_3755_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 1);
                crate::leanh::lean_closure_set(v___f_3755_, 0, v_name_3753_);
                v___x_3756_ = crate::leanh::lean_box(0);
                v___x_3757_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__0;
                v___x_3758_ = l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__1;
                v___x_3759_ = crate::leanh::lean_box((v_builtin_3752_) as usize);
                v___f_3760_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 11, 5);
                crate::leanh::lean_closure_set(v___f_3760_, 0, v___x_3759_);
                crate::leanh::lean_closure_set(v___f_3760_, 1, v___x_3756_);
                crate::leanh::lean_closure_set(v___f_3760_, 2, v___x_3757_);
                crate::leanh::lean_closure_set(v___f_3760_, 3, v___x_3758_);
                crate::leanh::lean_closure_set(v___f_3760_, 4, v_name_3753_);
                v___x_3761_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__24_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
                if v_builtin_3752_ == 0 {
                    v___x_3770_ = l_panic___at___00Lean_Server_CodeAction_getFileSource_x21_spec__0___closed__0;
                    v___y_3763_ = v___x_3770_;
                    state = 1;
                    continue;
                } else {
                    v___x_3771_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__26_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
                    v___y_3763_ = v___x_3771_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3764_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2___closed__25_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
                crate::leanh::lean_inc_ref(v___y_3763_);
                v___x_3765_ = lean_string_append(v___y_3763_, v___x_3764_);
                v___x_3766_ = 1;
                v___x_3767_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3767_, 0, v___x_3761_);
                crate::leanh::lean_ctor_set(v___x_3767_, 1, v_name_3753_);
                crate::leanh::lean_ctor_set(v___x_3767_, 2, v___x_3765_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3767_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3766_,
                );
                v___x_3768_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3767_);
                crate::leanh::lean_ctor_set(v___x_3768_, 1, v___f_3760_);
                crate::leanh::lean_ctor_set(v___x_3768_, 2, v___f_3755_);
                v___x_3769_ = l_Lean_registerBuiltinAttribute(v___x_3768_);
                return v___x_3769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(
    mut v_builtin_3772_: *mut crate::leanh::LeanObject,
    mut v_name_3773_: *mut crate::leanh::LeanObject,
    mut v___y_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_builtin_boxed_3775_: u8 = 0;
    let mut v_res_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3775_ = (crate::leanh::lean_unbox(v_builtin_3772_) as u8);
    v_res_3776_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v_builtin_boxed_3775_, v_name_3773_);
    return v_res_3776_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = 1;
    v___x_3785_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
    v___x_3786_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v___x_3784_, v___x_3785_);
    if crate::leanh::lean_obj_tag(v___x_3786_) == 0 {
        let mut v___x_3787_: u8 = 0;
        let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3786_, 1);
        v___x_3787_ = 0;
        v___x_3788_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_;
        v___x_3789_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___lam__2_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_(v___x_3787_, v___x_3788_);
        return v___x_3789_;
    } else {
        return v___x_3786_;
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2____boxed(
    mut v_a_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_();
    return v_res_3791_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_3792_: *mut crate::leanh::LeanObject,
    mut v_msg_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___redArg(v_msg_3793_, v___y_3794_, v___y_3795_);
    return v___x_3797_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_3798_: *mut crate::leanh::LeanObject,
    mut v_msg_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0(v_00_u03b1_3798_, v_msg_3799_, v___y_3800_, v___y_3801_);
    crate::leanh::lean_dec(v___y_3801_);
    crate::leanh::lean_dec_ref(v___y_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(
    mut v_00_u03b1_3804_: *mut crate::leanh::LeanObject,
    mut v_attrName_3805_: *mut crate::leanh::LeanObject,
    mut v_declName_3806_: *mut crate::leanh::LeanObject,
    mut v_givenType_3807_: *mut crate::leanh::LeanObject,
    mut v_expectedType_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___redArg(v_attrName_3805_, v_declName_3806_, v_givenType_3807_, v_expectedType_3808_, v___y_3809_, v___y_3810_);
    return v___x_3812_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3___boxed(
    mut v_00_u03b1_3813_: *mut crate::leanh::LeanObject,
    mut v_attrName_3814_: *mut crate::leanh::LeanObject,
    mut v_declName_3815_: *mut crate::leanh::LeanObject,
    mut v_givenType_3816_: *mut crate::leanh::LeanObject,
    mut v_expectedType_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__3(v_00_u03b1_3813_, v_attrName_3814_, v_declName_3815_, v_givenType_3816_, v_expectedType_3817_, v___y_3818_, v___y_3819_);
    crate::leanh::lean_dec(v___y_3819_);
    crate::leanh::lean_dec_ref(v___y_3818_);
    return v_res_3821_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(
    mut v_00_u03b1_3822_: *mut crate::leanh::LeanObject,
    mut v_name_3823_: *mut crate::leanh::LeanObject,
    mut v_kind_3824_: u8,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___redArg(v_name_3823_, v_kind_3824_, v___y_3825_, v___y_3826_);
    return v___x_3828_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4___boxed(
    mut v_00_u03b1_3829_: *mut crate::leanh::LeanObject,
    mut v_name_3830_: *mut crate::leanh::LeanObject,
    mut v_kind_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3835_: u8 = 0;
    let mut v_res_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3835_ = (crate::leanh::lean_unbox(v_kind_3831_) as u8);
    v_res_3836_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__4(v_00_u03b1_3829_, v_name_3830_, v_kind_boxed_3835_, v___y_3832_, v___y_3833_);
    crate::leanh::lean_dec(v___y_3833_);
    crate::leanh::lean_dec_ref(v___y_3832_);
    return v_res_3836_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(
    mut v_00_u03b1_3837_: *mut crate::leanh::LeanObject,
    mut v_constName_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_3838_, v___y_3839_, v___y_3840_);
    return v___x_3842_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_00_u03b1_3843_: *mut crate::leanh::LeanObject,
    mut v_constName_3844_: *mut crate::leanh::LeanObject,
    mut v___y_3845_: *mut crate::leanh::LeanObject,
    mut v___y_3846_: *mut crate::leanh::LeanObject,
    mut v___y_3847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3848_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_3843_, v_constName_3844_, v___y_3845_, v___y_3846_);
    crate::leanh::lean_dec(v___y_3846_);
    crate::leanh::lean_dec_ref(v___y_3845_);
    return v_res_3848_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(
    mut v_00_u03b1_3849_: *mut crate::leanh::LeanObject,
    mut v_ref_3850_: *mut crate::leanh::LeanObject,
    mut v_constName_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
    mut v___y_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3855_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_3850_, v_constName_3851_, v___y_3852_, v___y_3853_);
    return v___x_3855_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b1_3856_: *mut crate::leanh::LeanObject,
    mut v_ref_3857_: *mut crate::leanh::LeanObject,
    mut v_constName_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3862_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_3856_, v_ref_3857_, v_constName_3858_, v___y_3859_, v___y_3860_);
    crate::leanh::lean_dec(v___y_3860_);
    crate::leanh::lean_dec_ref(v___y_3859_);
    crate::leanh::lean_dec(v_ref_3857_);
    return v_res_3862_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(
    mut v_00_u03b1_3863_: *mut crate::leanh::LeanObject,
    mut v_ref_3864_: *mut crate::leanh::LeanObject,
    mut v_msg_3865_: *mut crate::leanh::LeanObject,
    mut v_declHint_3866_: *mut crate::leanh::LeanObject,
    mut v___y_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3864_, v_msg_3865_, v_declHint_3866_, v___y_3867_, v___y_3868_);
    return v___x_3870_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b1_3871_: *mut crate::leanh::LeanObject,
    mut v_ref_3872_: *mut crate::leanh::LeanObject,
    mut v_msg_3873_: *mut crate::leanh::LeanObject,
    mut v_declHint_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_3871_, v_ref_3872_, v_msg_3873_, v_declHint_3874_, v___y_3875_, v___y_3876_);
    crate::leanh::lean_dec(v___y_3876_);
    crate::leanh::lean_dec_ref(v___y_3875_);
    crate::leanh::lean_dec(v_ref_3872_);
    return v_res_3878_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(
    mut v_msg_3879_: *mut crate::leanh::LeanObject,
    mut v_declHint_3880_: *mut crate::leanh::LeanObject,
    mut v___y_3881_: *mut crate::leanh::LeanObject,
    mut v___y_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3879_, v_declHint_3880_, v___y_3882_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(
    mut v_msg_3885_: *mut crate::leanh::LeanObject,
    mut v_declHint_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
    mut v___y_3888_: *mut crate::leanh::LeanObject,
    mut v___y_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3890_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_3885_, v_declHint_3886_, v___y_3887_, v___y_3888_);
    crate::leanh::lean_dec(v___y_3888_);
    crate::leanh::lean_dec_ref(v___y_3887_);
    return v_res_3890_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(
    mut v_00_u03b1_3891_: *mut crate::leanh::LeanObject,
    mut v_ref_3892_: *mut crate::leanh::LeanObject,
    mut v_msg_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3897_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3892_, v_msg_3893_, v___y_3894_, v___y_3895_);
    return v___x_3897_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(
    mut v_00_u03b1_3898_: *mut crate::leanh::LeanObject,
    mut v_ref_3899_: *mut crate::leanh::LeanObject,
    mut v_msg_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_3898_, v_ref_3899_, v_msg_3900_, v___y_3901_, v___y_3902_);
    crate::leanh::lean_dec(v___y_3902_);
    crate::leanh::lean_dec_ref(v___y_3901_);
    crate::leanh::lean_dec(v_ref_3899_);
    return v_res_3904_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(
    mut v_inst_3909_: *mut crate::leanh::LeanObject,
    mut v_inst_3910_: *mut crate::leanh::LeanObject,
    mut v_inst_3911_: *mut crate::leanh::LeanObject,
    mut v_inst_3912_: *mut crate::leanh::LeanObject,
    mut v_declName_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0;
    v___x_3915_ = l_Lean_evalConstCheck___redArg(
        v_inst_3912_,
        v_inst_3909_,
        v_inst_3911_,
        v_inst_3910_,
        v___x_3914_,
        v_declName_3913_,
    );
    return v___x_3915_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe(
    mut v_M_3916_: *mut crate::leanh::LeanObject,
    mut v_inst_3917_: *mut crate::leanh::LeanObject,
    mut v_inst_3918_: *mut crate::leanh::LeanObject,
    mut v_inst_3919_: *mut crate::leanh::LeanObject,
    mut v_inst_3920_: *mut crate::leanh::LeanObject,
    mut v_declName_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3922_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg(v_inst_3917_, v_inst_3918_, v_inst_3919_, v_inst_3920_, v_declName_3921_);
    return v___x_3922_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(
    mut v___y_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_doc_3925_ = crate::leanh::lean_ctor_get(v___y_3923_, 1);
    crate::leanh::lean_inc_ref(v_doc_3925_);
    v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3926_, 0, v_doc_3925_);
    return v___x_3926_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6___boxed(
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v___y_3927_);
    crate::leanh::lean_dec_ref(v___y_3927_);
    return v_res_3929_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(
    mut v_init_3930_: *mut crate::leanh::LeanObject,
    mut v_x_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3931_) == 0 {
                    v_k_3932_ = crate::leanh::lean_ctor_get(v_x_3931_, 1);
                    v_v_3933_ = crate::leanh::lean_ctor_get(v_x_3931_, 2);
                    v_l_3934_ = crate::leanh::lean_ctor_get(v_x_3931_, 3);
                    v_r_3935_ = crate::leanh::lean_ctor_get(v_x_3931_, 4);
                    v___x_3936_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v_init_3930_, v_r_3935_);
                    crate::leanh::lean_inc(v_v_3933_);
                    crate::leanh::lean_inc(v_k_3932_);
                    v___x_3937_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3937_, 0, v_k_3932_);
                    crate::leanh::lean_ctor_set(v___x_3937_, 1, v_v_3933_);
                    v___x_3938_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3938_, 0, v___x_3937_);
                    crate::leanh::lean_ctor_set(v___x_3938_, 1, v___x_3936_);
                    v_init_3930_ = v___x_3938_;
                    v_x_3931_ = v_l_3934_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3930_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4___boxed(
    mut v_init_3940_: *mut crate::leanh::LeanObject,
    mut v_x_3941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(
        v_init_3940_,
        v_x_3941_,
    );
    crate::leanh::lean_dec(v_x_3941_);
    return v_res_3942_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(
    mut v___y_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = lean_st_ref_get(v___y_3944_);
    v_env_3947_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
    crate::leanh::lean_inc_ref(v_env_3947_);
    crate::leanh::lean_dec(v___x_3946_);
    v___x_3948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3948_, 0, v_env_3947_);
    v___x_3949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3949_, 0, v___x_3948_);
    return v___x_3949_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0___boxed(
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_3950_, v___y_3951_);
    crate::leanh::lean_dec(v___y_3951_);
    crate::leanh::lean_dec_ref(v___y_3950_);
    return v_res_3953_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3954_ = crate::leanh::lean_box(0);
    v___x_3955_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_3956_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3955_);
    crate::leanh::lean_ctor_set(v___x_3956_, 1, v___x_3954_);
    return v___x_3956_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___closed__0);
    v___x_3959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3959_, 0, v___x_3958_);
    return v___x_3959_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg___boxed(
    mut v___y_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
    return v_res_3961_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(
    mut v_msg_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3966_ = crate::leanh::lean_ctor_get(v___y_3963_, 5);
                v___x_3967_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2__spec__0_spec__0(v_msg_3962_, v___y_3963_, v___y_3964_);
                v_a_3968_ = crate::leanh::lean_ctor_get(v___x_3967_, 0);
                v_isSharedCheck_3976_ = (!crate::leanh::lean_is_exclusive(v___x_3967_)) as u8;
                if v_isSharedCheck_3976_ == 0 {
                    v___x_3970_ = v___x_3967_;
                    v_isShared_3971_ = v_isSharedCheck_3976_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3968_);
                    crate::leanh::lean_dec(v___x_3967_);
                    v___x_3970_ = crate::leanh::lean_box(0);
                    v_isShared_3971_ = v_isSharedCheck_3976_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3966_);
                v___x_3972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3972_, 0, v_ref_3966_);
                crate::leanh::lean_ctor_set(v___x_3972_, 1, v_a_3968_);
                if v_isShared_3971_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3970_, 1);
                    crate::leanh::lean_ctor_set(v___x_3970_, 0, v___x_3972_);
                    v___x_3974_ = v___x_3970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_msg_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
    mut v___y_3979_: *mut crate::leanh::LeanObject,
    mut v___y_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3981_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v_msg_3977_, v___y_3978_, v___y_3979_);
    crate::leanh::lean_dec(v___y_3979_);
    crate::leanh::lean_dec_ref(v___y_3978_);
    return v_res_3981_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(
    mut v_x_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3982_) == 0 {
                    v_a_3987_ = crate::leanh::lean_ctor_get(v_x_3982_, 0);
                    crate::leanh::lean_inc(v_a_3987_);
                    crate::leanh::lean_dec_ref_known(v_x_3982_, 1);
                    v___x_3988_ = l_Lean_stringToMessageData(v_a_3987_);
                    v___x_3989_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v___x_3988_, v___y_3984_, v___y_3985_);
                    return v___x_3989_;
                } else {
                    v_a_3990_ = crate::leanh::lean_ctor_get(v_x_3982_, 0);
                    v_isSharedCheck_3998_ = (!crate::leanh::lean_is_exclusive(v_x_3982_)) as u8;
                    if v_isSharedCheck_3998_ == 0 {
                        v___x_3992_ = v_x_3982_;
                        v_isShared_3993_ = v_isSharedCheck_3998_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3990_);
                        crate::leanh::lean_dec(v_x_3982_);
                        v___x_3992_ = crate::leanh::lean_box(0);
                        v_isShared_3993_ = v_isSharedCheck_3998_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3993_ == 0 {
                    v___x_3995_ = v___x_3992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3990_);
                    v___x_3995_ = v_reuseFailAlloc_3997_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3996_, 0, v___x_3995_);
                return v___x_3996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_x_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v_x_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
    crate::leanh::lean_dec(v___y_4002_);
    crate::leanh::lean_dec_ref(v___y_4001_);
    crate::leanh::lean_dec_ref(v___y_4000_);
    return v_res_4004_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(
    mut v_typeName_4005_: *mut crate::leanh::LeanObject,
    mut v_constName_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4018_: u8 = 0;
    let mut v_a_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut v_a_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4038_: u8 = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v_a_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4051_: u8 = 0;
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v_a_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4079_: u8 = 0;
    let mut v_a_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4087_: u8 = 0;
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v_a_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4011_ = lean_st_ref_get(v___y_4009_);
                v_env_4012_ = crate::leanh::lean_ctor_get(v___x_4011_, 0);
                crate::leanh::lean_inc_ref(v_env_4012_);
                crate::leanh::lean_dec(v___x_4011_);
                crate::leanh::lean_inc(v_constName_4006_);
                v___x_4013_ = lean_has_compile_error(v_env_4012_, v_constName_4006_);
                if v___x_4013_ == 0 {
                    v___x_4014_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_4008_, v___y_4009_);
                    if crate::leanh::lean_obj_tag(v___x_4014_) == 0 {
                        v_a_4015_ = crate::leanh::lean_ctor_get(v___x_4014_, 0);
                        v_isSharedCheck_4034_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4014_)) as u8;
                        if v_isSharedCheck_4034_ == 0 {
                            v___x_4017_ = v___x_4014_;
                            v_isShared_4018_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4015_);
                            crate::leanh::lean_dec(v___x_4014_);
                            v___x_4017_ = crate::leanh::lean_box(0);
                            v_isShared_4018_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_constName_4006_);
                        crate::leanh::lean_dec(v_typeName_4005_);
                        v_a_4035_ = crate::leanh::lean_ctor_get(v___x_4014_, 0);
                        v_isSharedCheck_4042_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4014_)) as u8;
                        if v_isSharedCheck_4042_ == 0 {
                            v___x_4037_ = v___x_4014_;
                            v_isShared_4038_ = v_isSharedCheck_4042_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4035_);
                            crate::leanh::lean_dec(v___x_4014_);
                            v___x_4037_ = crate::leanh::lean_box(0);
                            v_isShared_4038_ = v_isSharedCheck_4042_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_4043_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
                    if crate::leanh::lean_obj_tag(v___x_4043_) == 0 {
                        v_a_4044_ = crate::leanh::lean_ctor_get(v___x_4043_, 0);
                        v_isSharedCheck_4088_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4043_)) as u8;
                        if v_isSharedCheck_4088_ == 0 {
                            v___x_4046_ = v___x_4043_;
                            v_isShared_4047_ = v_isSharedCheck_4088_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4044_);
                            crate::leanh::lean_dec(v___x_4043_);
                            v___x_4046_ = crate::leanh::lean_box(0);
                            v_isShared_4047_ = v_isSharedCheck_4088_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_constName_4006_);
                        crate::leanh::lean_dec(v_typeName_4005_);
                        v_a_4089_ = crate::leanh::lean_ctor_get(v___x_4043_, 0);
                        v_isSharedCheck_4096_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4043_)) as u8;
                        if v_isSharedCheck_4096_ == 0 {
                            v___x_4091_ = v___x_4043_;
                            v_isShared_4092_ = v_isSharedCheck_4096_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4089_);
                            crate::leanh::lean_dec(v___x_4043_);
                            v___x_4091_ = crate::leanh::lean_box(0);
                            v_isShared_4092_ = v_isSharedCheck_4096_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4015_) == 0 {
                    crate::leanh::lean_dec(v_constName_4006_);
                    crate::leanh::lean_dec(v_typeName_4005_);
                    v_a_4019_ = crate::leanh::lean_ctor_get(v_a_4015_, 0);
                    v_isSharedCheck_4029_ = (!crate::leanh::lean_is_exclusive(v_a_4015_)) as u8;
                    if v_isSharedCheck_4029_ == 0 {
                        v___x_4021_ = v_a_4015_;
                        v_isShared_4022_ = v_isSharedCheck_4029_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4019_);
                        crate::leanh::lean_dec(v_a_4015_);
                        v___x_4021_ = crate::leanh::lean_box(0);
                        v_isShared_4022_ = v_isSharedCheck_4029_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4017_);
                    v_a_4030_ = crate::leanh::lean_ctor_get(v_a_4015_, 0);
                    crate::leanh::lean_inc(v_a_4030_);
                    crate::leanh::lean_dec_ref_known(v_a_4015_, 1);
                    v_options_4031_ = crate::leanh::lean_ctor_get(v___y_4008_, 2);
                    v___x_4032_ = l_Lean_Environment_evalConstCheck___redArg(
                        v_a_4030_,
                        v_options_4031_,
                        v_typeName_4005_,
                        v_constName_4006_,
                    );
                    v___x_4033_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v___x_4032_, v___y_4007_, v___y_4008_, v___y_4009_);
                    return v___x_4033_;
                }
            }
            2 => {
                if v_isShared_4022_ == 0 {
                    v___x_4024_ = v___x_4021_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4019_);
                    v___x_4024_ = v_reuseFailAlloc_4028_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4018_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4017_, 0, v___x_4024_);
                    v___x_4026_ = v___x_4017_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4026_;
            }
            5 => {
                if v_isShared_4038_ == 0 {
                    v___x_4040_ = v___x_4037_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
                    v___x_4040_ = v_reuseFailAlloc_4041_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4040_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_4044_) == 0 {
                    crate::leanh::lean_dec(v_constName_4006_);
                    crate::leanh::lean_dec(v_typeName_4005_);
                    v_a_4048_ = crate::leanh::lean_ctor_get(v_a_4044_, 0);
                    v_isSharedCheck_4058_ = (!crate::leanh::lean_is_exclusive(v_a_4044_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4050_ = v_a_4044_;
                        v_isShared_4051_ = v_isSharedCheck_4058_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4048_);
                        crate::leanh::lean_dec(v_a_4044_);
                        v___x_4050_ = crate::leanh::lean_box(0);
                        v_isShared_4051_ = v_isSharedCheck_4058_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_4044_, 1);
                    crate::leanh::lean_del_object(v___x_4046_);
                    v___x_4059_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___lam__0(v___y_4008_, v___y_4009_);
                    if crate::leanh::lean_obj_tag(v___x_4059_) == 0 {
                        v_a_4060_ = crate::leanh::lean_ctor_get(v___x_4059_, 0);
                        v_isSharedCheck_4079_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4059_)) as u8;
                        if v_isSharedCheck_4079_ == 0 {
                            v___x_4062_ = v___x_4059_;
                            v_isShared_4063_ = v_isSharedCheck_4079_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4060_);
                            crate::leanh::lean_dec(v___x_4059_);
                            v___x_4062_ = crate::leanh::lean_box(0);
                            v_isShared_4063_ = v_isSharedCheck_4079_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_constName_4006_);
                        crate::leanh::lean_dec(v_typeName_4005_);
                        v_a_4080_ = crate::leanh::lean_ctor_get(v___x_4059_, 0);
                        v_isSharedCheck_4087_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4059_)) as u8;
                        if v_isSharedCheck_4087_ == 0 {
                            v___x_4082_ = v___x_4059_;
                            v_isShared_4083_ = v_isSharedCheck_4087_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4080_);
                            crate::leanh::lean_dec(v___x_4059_);
                            v___x_4082_ = crate::leanh::lean_box(0);
                            v_isShared_4083_ = v_isSharedCheck_4087_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_4051_ == 0 {
                    v___x_4053_ = v___x_4050_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4048_);
                    v___x_4053_ = v_reuseFailAlloc_4057_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4046_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4046_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
                    v___x_4055_ = v_reuseFailAlloc_4056_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4055_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_a_4060_) == 0 {
                    crate::leanh::lean_dec(v_constName_4006_);
                    crate::leanh::lean_dec(v_typeName_4005_);
                    v_a_4064_ = crate::leanh::lean_ctor_get(v_a_4060_, 0);
                    v_isSharedCheck_4074_ = (!crate::leanh::lean_is_exclusive(v_a_4060_)) as u8;
                    if v_isSharedCheck_4074_ == 0 {
                        v___x_4066_ = v_a_4060_;
                        v_isShared_4067_ = v_isSharedCheck_4074_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4064_);
                        crate::leanh::lean_dec(v_a_4060_);
                        v___x_4066_ = crate::leanh::lean_box(0);
                        v_isShared_4067_ = v_isSharedCheck_4074_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4062_);
                    v_a_4075_ = crate::leanh::lean_ctor_get(v_a_4060_, 0);
                    crate::leanh::lean_inc(v_a_4075_);
                    crate::leanh::lean_dec_ref_known(v_a_4060_, 1);
                    v_options_4076_ = crate::leanh::lean_ctor_get(v___y_4008_, 2);
                    v___x_4077_ = l_Lean_Environment_evalConstCheck___redArg(
                        v_a_4075_,
                        v_options_4076_,
                        v_typeName_4005_,
                        v_constName_4006_,
                    );
                    v___x_4078_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v___x_4077_, v___y_4007_, v___y_4008_, v___y_4009_);
                    return v___x_4078_;
                }
            }
            12 => {
                if v_isShared_4067_ == 0 {
                    v___x_4069_ = v___x_4066_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4073_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4062_, 0, v___x_4069_);
                    v___x_4071_ = v___x_4062_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4069_);
                    v___x_4071_ = v_reuseFailAlloc_4072_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4071_;
            }
            15 => {
                if v_isShared_4083_ == 0 {
                    v___x_4085_ = v___x_4082_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
                    v___x_4085_ = v_reuseFailAlloc_4086_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4085_;
            }
            17 => {
                if v_isShared_4092_ == 0 {
                    v___x_4094_ = v___x_4091_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
                    v___x_4094_ = v_reuseFailAlloc_4095_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg___boxed(
    mut v_typeName_4097_: *mut crate::leanh::LeanObject,
    mut v_constName_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4103_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v_typeName_4097_, v_constName_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
    crate::leanh::lean_dec(v___y_4101_);
    crate::leanh::lean_dec_ref(v___y_4100_);
    crate::leanh::lean_dec_ref(v___y_4099_);
    return v_res_4103_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(
    mut v_declName_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4109_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___redArg___closed__0;
    v___x_4110_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v___x_4109_, v_declName_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
    return v___x_4110_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed(
    mut v_declName_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4116_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(v_declName_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
    crate::leanh::lean_dec(v___y_4114_);
    crate::leanh::lean_dec_ref(v___y_4113_);
    crate::leanh::lean_dec_ref(v___y_4112_);
    return v_res_4116_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(
    mut v_sz_4117_: usize,
    mut v_i_4118_: usize,
    mut v_bs_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v_a_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut v_a_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: usize = 0;
    let mut v___x_4148_: usize = 0;
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4151_: u8 = 0;
    let mut v_a_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4124_ = lean_usize_dec_lt(v_i_4118_, v_sz_4117_);
                if v___x_4124_ == 0 {
                    v___x_4125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4125_, 0, v_bs_4119_);
                    v___x_4126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4126_, 0, v___x_4125_);
                    return v___x_4126_;
                } else {
                    v_v_4127_ = lean_array_uget_borrowed(v_bs_4119_, v_i_4118_);
                    crate::leanh::lean_inc(v_v_4127_);
                    v___x_4128_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2(v_v_4127_, v___y_4120_, v___y_4121_, v___y_4122_);
                    if crate::leanh::lean_obj_tag(v___x_4128_) == 0 {
                        v_a_4129_ = crate::leanh::lean_ctor_get(v___x_4128_, 0);
                        v_isSharedCheck_4151_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4128_)) as u8;
                        if v_isSharedCheck_4151_ == 0 {
                            v___x_4131_ = v___x_4128_;
                            v_isShared_4132_ = v_isSharedCheck_4151_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4129_);
                            crate::leanh::lean_dec(v___x_4128_);
                            v___x_4131_ = crate::leanh::lean_box(0);
                            v_isShared_4132_ = v_isSharedCheck_4151_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4119_);
                        v_a_4152_ = crate::leanh::lean_ctor_get(v___x_4128_, 0);
                        v_isSharedCheck_4159_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4128_)) as u8;
                        if v_isSharedCheck_4159_ == 0 {
                            v___x_4154_ = v___x_4128_;
                            v_isShared_4155_ = v_isSharedCheck_4159_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4152_);
                            crate::leanh::lean_dec(v___x_4128_);
                            v___x_4154_ = crate::leanh::lean_box(0);
                            v_isShared_4155_ = v_isSharedCheck_4159_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4129_) == 0 {
                    crate::leanh::lean_dec_ref(v_bs_4119_);
                    v_a_4133_ = crate::leanh::lean_ctor_get(v_a_4129_, 0);
                    v_isSharedCheck_4143_ = (!crate::leanh::lean_is_exclusive(v_a_4129_)) as u8;
                    if v_isSharedCheck_4143_ == 0 {
                        v___x_4135_ = v_a_4129_;
                        v_isShared_4136_ = v_isSharedCheck_4143_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4133_);
                        crate::leanh::lean_dec(v_a_4129_);
                        v___x_4135_ = crate::leanh::lean_box(0);
                        v_isShared_4136_ = v_isSharedCheck_4143_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4131_);
                    v_a_4144_ = crate::leanh::lean_ctor_get(v_a_4129_, 0);
                    crate::leanh::lean_inc(v_a_4144_);
                    crate::leanh::lean_dec_ref_known(v_a_4129_, 1);
                    v___x_4145_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4146_ = lean_array_uset(v_bs_4119_, v_i_4118_, v___x_4145_);
                    v___x_4147_ = 1usize;
                    v___x_4148_ = lean_usize_add(v_i_4118_, v___x_4147_);
                    v___x_4149_ = lean_array_uset(v_bs_x27_4146_, v_i_4118_, v_a_4144_);
                    v_i_4118_ = v___x_4148_;
                    v_bs_4119_ = v___x_4149_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_4136_ == 0 {
                    v___x_4138_ = v___x_4135_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4133_);
                    v___x_4138_ = v_reuseFailAlloc_4142_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4131_, 0, v___x_4138_);
                    v___x_4140_ = v___x_4131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4138_);
                    v___x_4140_ = v_reuseFailAlloc_4141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4140_;
            }
            5 => {
                if v_isShared_4155_ == 0 {
                    v___x_4157_ = v___x_4154_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
                    v___x_4157_ = v_reuseFailAlloc_4158_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3___boxed(
    mut v_sz_4160_: *mut crate::leanh::LeanObject,
    mut v_i_4161_: *mut crate::leanh::LeanObject,
    mut v_bs_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
    mut v___y_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4167_: usize = 0;
    let mut v_i_boxed_4168_: usize = 0;
    let mut v_res_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4167_ = crate::leanh::lean_unbox_usize(v_sz_4160_);
    crate::leanh::lean_dec(v_sz_4160_);
    v_i_boxed_4168_ = crate::leanh::lean_unbox_usize(v_i_4161_);
    crate::leanh::lean_dec(v_i_4161_);
    v_res_4169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(v_sz_boxed_4167_, v_i_boxed_4168_, v_bs_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
    crate::leanh::lean_dec(v___y_4165_);
    crate::leanh::lean_dec_ref(v___y_4164_);
    crate::leanh::lean_dec_ref(v___y_4163_);
    return v_res_4169_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(
    mut v_init_4170_: *mut crate::leanh::LeanObject,
    mut v_x_4171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4171_) == 0 {
                    v_k_4172_ = crate::leanh::lean_ctor_get(v_x_4171_, 1);
                    crate::leanh::lean_inc(v_k_4172_);
                    v_l_4173_ = crate::leanh::lean_ctor_get(v_x_4171_, 3);
                    crate::leanh::lean_inc(v_l_4173_);
                    v_r_4174_ = crate::leanh::lean_ctor_get(v_x_4171_, 4);
                    crate::leanh::lean_inc(v_r_4174_);
                    crate::leanh::lean_dec_ref_known(v_x_4171_, 5);
                    v___x_4175_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v_init_4170_, v_l_4173_);
                    v___x_4176_ = lean_array_push(v___x_4175_, v_k_4172_);
                    v_init_4170_ = v___x_4176_;
                    v_x_4171_ = v_r_4174_;
                    state = 0;
                    continue;
                } else {
                    return v_init_4170_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__0(
    mut v___x_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4194_: usize = 0;
    let mut v___x_4195_: usize = 0;
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v_a_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut v_a_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4215_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_a_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_size_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4183_ = lean_st_ref_get(v___y_4181_);
                v_env_4184_ = crate::leanh::lean_ctor_get(v___x_4183_, 0);
                crate::leanh::lean_inc_ref(v_env_4184_);
                crate::leanh::lean_dec(v___x_4183_);
                v___x_4185_ = l_Lean_Server_codeActionProviderExt;
                v_toEnvExtension_4186_ = crate::leanh::lean_ctor_get(v___x_4185_, 0);
                v_asyncMode_4187_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4186_, 2);
                v___x_4188_ = crate::leanh::lean_box(0);
                v___x_4189_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4178_,
                    v___x_4185_,
                    v_env_4184_,
                    v_asyncMode_4187_,
                    v___x_4188_,
                );
                if crate::leanh::lean_obj_tag(v___x_4189_) == 0 {
                    v_size_4239_ = crate::leanh::lean_ctor_get(v___x_4189_, 0);
                    crate::leanh::lean_inc(v_size_4239_);
                    v___y_4191_ = v_size_4239_;
                    state = 1;
                    continue;
                } else {
                    v___x_4240_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4191_ = v___x_4240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4192_ = lean_mk_empty_array_with_capacity(v___y_4191_);
                crate::leanh::lean_dec(v___y_4191_);
                v___x_4193_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v___x_4192_, v___x_4189_);
                v_sz_4194_ = lean_array_size(v___x_4193_);
                v___x_4195_ = 0usize;
                crate::leanh::lean_inc_ref(v___x_4193_);
                v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_handleCodeAction_spec__3(v_sz_4194_, v___x_4195_, v___x_4193_, v___y_4179_, v___y_4180_, v___y_4181_);
                if crate::leanh::lean_obj_tag(v___x_4196_) == 0 {
                    v_a_4197_ = crate::leanh::lean_ctor_get(v___x_4196_, 0);
                    v_isSharedCheck_4230_ = (!crate::leanh::lean_is_exclusive(v___x_4196_)) as u8;
                    if v_isSharedCheck_4230_ == 0 {
                        v___x_4199_ = v___x_4196_;
                        v_isShared_4200_ = v_isSharedCheck_4230_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4197_);
                        crate::leanh::lean_dec(v___x_4196_);
                        v___x_4199_ = crate::leanh::lean_box(0);
                        v_isShared_4200_ = v_isSharedCheck_4230_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4193_);
                    v_a_4231_ = crate::leanh::lean_ctor_get(v___x_4196_, 0);
                    v_isSharedCheck_4238_ = (!crate::leanh::lean_is_exclusive(v___x_4196_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v___x_4233_ = v___x_4196_;
                        v_isShared_4234_ = v_isSharedCheck_4238_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4231_);
                        crate::leanh::lean_dec(v___x_4196_);
                        v___x_4233_ = crate::leanh::lean_box(0);
                        v_isShared_4234_ = v_isSharedCheck_4238_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4197_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_4193_);
                    v_a_4201_ = crate::leanh::lean_ctor_get(v_a_4197_, 0);
                    v_isSharedCheck_4211_ = (!crate::leanh::lean_is_exclusive(v_a_4197_)) as u8;
                    if v_isSharedCheck_4211_ == 0 {
                        v___x_4203_ = v_a_4197_;
                        v_isShared_4204_ = v_isSharedCheck_4211_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4201_);
                        crate::leanh::lean_dec(v_a_4197_);
                        v___x_4203_ = crate::leanh::lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4211_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4212_ = crate::leanh::lean_ctor_get(v_a_4197_, 0);
                    v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v_a_4197_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4214_ = v_a_4197_;
                        v_isShared_4215_ = v_isSharedCheck_4229_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4212_);
                        crate::leanh::lean_dec(v_a_4197_);
                        v___x_4214_ = crate::leanh::lean_box(0);
                        v_isShared_4215_ = v_isSharedCheck_4229_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4204_ == 0 {
                    v___x_4206_ = v___x_4203_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4201_);
                    v___x_4206_ = v_reuseFailAlloc_4210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4206_);
                    v___x_4208_ = v___x_4199_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4208_;
            }
            6 => {
                v___x_4216_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
                v___x_4217_ = lean_st_ref_get(v___x_4216_);
                v___x_4218_ = crate::leanh::lean_box(0);
                v___x_4219_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_handleCodeAction_spec__4(v___x_4218_, v___x_4217_);
                crate::leanh::lean_dec(v___x_4217_);
                v___x_4220_ = lean_array_mk(v___x_4219_);
                v___x_4221_ = l_Array_zip___redArg(v___x_4193_, v_a_4212_);
                crate::leanh::lean_dec(v_a_4212_);
                crate::leanh::lean_dec_ref(v___x_4193_);
                v___x_4222_ = l_Array_append___redArg(v___x_4220_, v___x_4221_);
                crate::leanh::lean_dec_ref(v___x_4221_);
                if v_isShared_4215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4214_, 0, v___x_4222_);
                    v___x_4224_ = v___x_4214_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4222_);
                    v___x_4224_ = v_reuseFailAlloc_4228_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4224_);
                    v___x_4226_ = v___x_4199_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
                    v___x_4226_ = v_reuseFailAlloc_4227_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4226_;
            }
            9 => {
                if v_isShared_4234_ == 0 {
                    v___x_4236_ = v___x_4233_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
                    v___x_4236_ = v_reuseFailAlloc_4237_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__0___boxed(
    mut v___x_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4246_ =
        l_Lean_Server_handleCodeAction___lam__0(v___x_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
    crate::leanh::lean_dec(v___y_4244_);
    crate::leanh::lean_dec_ref(v___y_4243_);
    crate::leanh::lean_dec_ref(v___y_4242_);
    return v_res_4246_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(
    mut v_params_4247_: *mut crate::leanh::LeanObject,
    mut v_fst_4248_: *mut crate::leanh::LeanObject,
    mut v_as_4249_: *mut crate::leanh::LeanObject,
    mut v_i_4250_: *mut crate::leanh::LeanObject,
    mut v_j_4251_: *mut crate::leanh::LeanObject,
    mut v_bs_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4255_: u8 = 0;
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eager_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toWorkDoneProgressParams_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPartialResultParams_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_x3f_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreferred_x3f_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disabled_x3f_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_edit_x3f_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_command_x3f_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v_one_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_unused_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4254_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4255_ = lean_nat_dec_eq(v_i_4250_, v_zero_4254_);
                if v_isZero_4255_ == 1 {
                    crate::leanh::lean_dec(v_j_4251_);
                    crate::leanh::lean_dec(v_i_4250_);
                    crate::leanh::lean_dec(v_fst_4248_);
                    crate::leanh::lean_dec_ref(v_params_4247_);
                    v___x_4256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4256_, 0, v_bs_4252_);
                    return v___x_4256_;
                } else {
                    v___x_4257_ = lean_array_fget_borrowed(v_as_4249_, v_j_4251_);
                    v_eager_4258_ = crate::leanh::lean_ctor_get(v___x_4257_, 0);
                    crate::leanh::lean_inc_ref(v_eager_4258_);
                    v_toWorkDoneProgressParams_4259_ =
                        crate::leanh::lean_ctor_get(v_eager_4258_, 0);
                    v_toPartialResultParams_4260_ = crate::leanh::lean_ctor_get(v_eager_4258_, 1);
                    v_title_4261_ = crate::leanh::lean_ctor_get(v_eager_4258_, 2);
                    v_kind_x3f_4262_ = crate::leanh::lean_ctor_get(v_eager_4258_, 3);
                    v_diagnostics_x3f_4263_ = crate::leanh::lean_ctor_get(v_eager_4258_, 4);
                    v_isPreferred_x3f_4264_ = crate::leanh::lean_ctor_get(v_eager_4258_, 5);
                    v_disabled_x3f_4265_ = crate::leanh::lean_ctor_get(v_eager_4258_, 6);
                    v_edit_x3f_4266_ = crate::leanh::lean_ctor_get(v_eager_4258_, 7);
                    v_command_x3f_4267_ = crate::leanh::lean_ctor_get(v_eager_4258_, 8);
                    v_isSharedCheck_4282_ = (!crate::leanh::lean_is_exclusive(v_eager_4258_)) as u8;
                    if v_isSharedCheck_4282_ == 0 {
                        v_unused_4283_ = crate::leanh::lean_ctor_get(v_eager_4258_, 9);
                        crate::leanh::lean_dec(v_unused_4283_);
                        v___x_4269_ = v_eager_4258_;
                        v_isShared_4270_ = v_isSharedCheck_4282_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_command_x3f_4267_);
                        crate::leanh::lean_inc(v_edit_x3f_4266_);
                        crate::leanh::lean_inc(v_disabled_x3f_4265_);
                        crate::leanh::lean_inc(v_isPreferred_x3f_4264_);
                        crate::leanh::lean_inc(v_diagnostics_x3f_4263_);
                        crate::leanh::lean_inc(v_kind_x3f_4262_);
                        crate::leanh::lean_inc(v_title_4261_);
                        crate::leanh::lean_inc(v_toPartialResultParams_4260_);
                        crate::leanh::lean_inc(v_toWorkDoneProgressParams_4259_);
                        crate::leanh::lean_dec(v_eager_4258_);
                        v___x_4269_ = crate::leanh::lean_box(0);
                        v_isShared_4270_ = v_isSharedCheck_4282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_4271_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_4272_ = lean_nat_sub(v_i_4250_, v_one_4271_);
                crate::leanh::lean_dec(v_i_4250_);
                crate::leanh::lean_inc(v_j_4251_);
                crate::leanh::lean_inc(v_fst_4248_);
                crate::leanh::lean_inc_ref(v_params_4247_);
                v___x_4273_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4273_, 0, v_params_4247_);
                crate::leanh::lean_ctor_set(v___x_4273_, 1, v_fst_4248_);
                crate::leanh::lean_ctor_set(v___x_4273_, 2, v_j_4251_);
                v___x_4274_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_4273_);
                v___x_4275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4274_);
                if v_isShared_4270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4269_, 9, v___x_4275_);
                    v___x_4277_ = v___x_4269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4281_,
                        0,
                        v_toWorkDoneProgressParams_4259_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4281_,
                        1,
                        v_toPartialResultParams_4260_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 2, v_title_4261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 3, v_kind_x3f_4262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 4, v_diagnostics_x3f_4263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 5, v_isPreferred_x3f_4264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 6, v_disabled_x3f_4265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 7, v_edit_x3f_4266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 8, v_command_x3f_4267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 9, v___x_4275_);
                    v___x_4277_ = v_reuseFailAlloc_4281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4278_ = lean_nat_add(v_j_4251_, v_one_4271_);
                crate::leanh::lean_dec(v_j_4251_);
                v___x_4279_ = lean_array_push(v_bs_4252_, v___x_4277_);
                v_i_4250_ = v_n_4272_;
                v_j_4251_ = v___x_4278_;
                v_bs_4252_ = v___x_4279_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg___boxed(
    mut v_params_4284_: *mut crate::leanh::LeanObject,
    mut v_fst_4285_: *mut crate::leanh::LeanObject,
    mut v_as_4286_: *mut crate::leanh::LeanObject,
    mut v_i_4287_: *mut crate::leanh::LeanObject,
    mut v_j_4288_: *mut crate::leanh::LeanObject,
    mut v_bs_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4291_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(
        v_params_4284_,
        v_fst_4285_,
        v_as_4286_,
        v_i_4287_,
        v_j_4288_,
        v_bs_4289_,
    );
    crate::leanh::lean_dec_ref(v_as_4286_);
    return v_res_4291_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(
    mut v_params_4292_: *mut crate::leanh::LeanObject,
    mut v_snap_4293_: *mut crate::leanh::LeanObject,
    mut v_as_4294_: *mut crate::leanh::LeanObject,
    mut v_i_4295_: usize,
    mut v_stop_4296_: usize,
    mut v_b_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: usize = 0;
    let mut v___x_4303_: usize = 0;
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v_a_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4330_: u8 = 0;
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4334_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4305_ = lean_usize_dec_eq(v_i_4295_, v_stop_4296_);
                if v___x_4305_ == 0 {
                    v___x_4306_ = lean_array_uget_borrowed(v_as_4294_, v_i_4295_);
                    v_fst_4307_ = crate::leanh::lean_ctor_get(v___x_4306_, 0);
                    v_snd_4308_ = crate::leanh::lean_ctor_get(v___x_4306_, 1);
                    v___x_4309_ = l_Lean_Server_RequestM_checkCancelled(v___y_4298_);
                    if crate::leanh::lean_obj_tag(v___x_4309_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4309_, 1);
                        crate::leanh::lean_inc(v_snd_4308_);
                        crate::leanh::lean_inc_ref(v___y_4298_);
                        crate::leanh::lean_inc_ref(v_snap_4293_);
                        crate::leanh::lean_inc_ref(v_params_4292_);
                        v___x_4310_ = crate::leanh::lean_apply_4(
                            v_snd_4308_,
                            v_params_4292_,
                            v_snap_4293_,
                            v___y_4298_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4310_) == 0 {
                            v_a_4311_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                            crate::leanh::lean_inc(v_a_4311_);
                            crate::leanh::lean_dec_ref_known(v___x_4310_, 1);
                            v___x_4312_ = lean_array_get_size(v_a_4311_);
                            v___x_4313_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4314_ = lean_mk_empty_array_with_capacity(v___x_4312_);
                            crate::leanh::lean_inc(v_fst_4307_);
                            crate::leanh::lean_inc_ref(v_params_4292_);
                            v___x_4315_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(v_params_4292_, v_fst_4307_, v_a_4311_, v___x_4312_, v___x_4313_, v___x_4314_);
                            crate::leanh::lean_dec(v_a_4311_);
                            if crate::leanh::lean_obj_tag(v___x_4315_) == 0 {
                                v_a_4316_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                                crate::leanh::lean_inc(v_a_4316_);
                                crate::leanh::lean_dec_ref_known(v___x_4315_, 1);
                                v___x_4317_ = l_Array_append___redArg(v_b_4297_, v_a_4316_);
                                crate::leanh::lean_dec(v_a_4316_);
                                v_a_4301_ = v___x_4317_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_4297_);
                                if crate::leanh::lean_obj_tag(v___x_4315_) == 0 {
                                    v_a_4318_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                                    crate::leanh::lean_inc(v_a_4318_);
                                    crate::leanh::lean_dec_ref_known(v___x_4315_, 1);
                                    v_a_4301_ = v_a_4318_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_snap_4293_);
                                    crate::leanh::lean_dec_ref(v_params_4292_);
                                    return v___x_4315_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_4297_);
                            crate::leanh::lean_dec_ref(v_snap_4293_);
                            crate::leanh::lean_dec_ref(v_params_4292_);
                            v_a_4319_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                            v_isSharedCheck_4326_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4310_)) as u8;
                            if v_isSharedCheck_4326_ == 0 {
                                v___x_4321_ = v___x_4310_;
                                v_isShared_4322_ = v_isSharedCheck_4326_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4319_);
                                crate::leanh::lean_dec(v___x_4310_);
                                v___x_4321_ = crate::leanh::lean_box(0);
                                v_isShared_4322_ = v_isSharedCheck_4326_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4297_);
                        crate::leanh::lean_dec_ref(v_snap_4293_);
                        crate::leanh::lean_dec_ref(v_params_4292_);
                        v_a_4327_ = crate::leanh::lean_ctor_get(v___x_4309_, 0);
                        v_isSharedCheck_4334_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4309_)) as u8;
                        if v_isSharedCheck_4334_ == 0 {
                            v___x_4329_ = v___x_4309_;
                            v_isShared_4330_ = v_isSharedCheck_4334_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4327_);
                            crate::leanh::lean_dec(v___x_4309_);
                            v___x_4329_ = crate::leanh::lean_box(0);
                            v_isShared_4330_ = v_isSharedCheck_4334_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snap_4293_);
                    crate::leanh::lean_dec_ref(v_params_4292_);
                    v___x_4335_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4335_, 0, v_b_4297_);
                    return v___x_4335_;
                }
            }
            1 => {
                v___x_4302_ = 1usize;
                v___x_4303_ = lean_usize_add(v_i_4295_, v___x_4302_);
                v_i_4295_ = v___x_4303_;
                v_b_4297_ = v_a_4301_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4322_ == 0 {
                    v___x_4324_ = v___x_4321_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
                    v___x_4324_ = v_reuseFailAlloc_4325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4324_;
            }
            4 => {
                if v_isShared_4330_ == 0 {
                    v___x_4332_ = v___x_4329_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
                    v___x_4332_ = v_reuseFailAlloc_4333_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5___boxed(
    mut v_params_4336_: *mut crate::leanh::LeanObject,
    mut v_snap_4337_: *mut crate::leanh::LeanObject,
    mut v_as_4338_: *mut crate::leanh::LeanObject,
    mut v_i_4339_: *mut crate::leanh::LeanObject,
    mut v_stop_4340_: *mut crate::leanh::LeanObject,
    mut v_b_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4344_: usize = 0;
    let mut v_stop_boxed_4345_: usize = 0;
    let mut v_res_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4344_ = crate::leanh::lean_unbox_usize(v_i_4339_);
    crate::leanh::lean_dec(v_i_4339_);
    v_stop_boxed_4345_ = crate::leanh::lean_unbox_usize(v_stop_4340_);
    crate::leanh::lean_dec(v_stop_4340_);
    v_res_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_4336_, v_snap_4337_, v_as_4338_, v_i_boxed_4344_, v_stop_boxed_4345_, v_b_4341_, v___y_4342_);
    crate::leanh::lean_dec_ref(v___y_4342_);
    crate::leanh::lean_dec_ref(v_as_4338_);
    return v_res_4346_;
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__1(
    mut v___f_4349_: *mut crate::leanh::LeanObject,
    mut v_params_4350_: *mut crate::leanh::LeanObject,
    mut v_snap_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: usize = 0;
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: usize = 0;
    let mut v___x_4374_: usize = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_a_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_snap_4351_);
                v___x_4354_ = l_Lean_Server_RequestM_runCoreM___redArg(
                    v_snap_4351_,
                    v___f_4349_,
                    v___y_4352_,
                );
                if crate::leanh::lean_obj_tag(v___x_4354_) == 0 {
                    v_a_4355_ = crate::leanh::lean_ctor_get(v___x_4354_, 0);
                    v_isSharedCheck_4376_ = (!crate::leanh::lean_is_exclusive(v___x_4354_)) as u8;
                    if v_isSharedCheck_4376_ == 0 {
                        v___x_4357_ = v___x_4354_;
                        v_isShared_4358_ = v_isSharedCheck_4376_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4355_);
                        crate::leanh::lean_dec(v___x_4354_);
                        v___x_4357_ = crate::leanh::lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4376_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snap_4351_);
                    crate::leanh::lean_dec_ref(v_params_4350_);
                    v_a_4377_ = crate::leanh::lean_ctor_get(v___x_4354_, 0);
                    v_isSharedCheck_4384_ = (!crate::leanh::lean_is_exclusive(v___x_4354_)) as u8;
                    if v_isSharedCheck_4384_ == 0 {
                        v___x_4379_ = v___x_4354_;
                        v_isShared_4380_ = v_isSharedCheck_4384_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4377_);
                        crate::leanh::lean_dec(v___x_4354_);
                        v___x_4379_ = crate::leanh::lean_box(0);
                        v_isShared_4380_ = v_isSharedCheck_4384_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4359_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4360_ = l_Lean_Server_handleCodeAction___lam__1___closed__0;
                v___x_4361_ = lean_array_get_size(v_a_4355_);
                v___x_4362_ = lean_nat_dec_lt(v___x_4359_, v___x_4361_);
                if v___x_4362_ == 0 {
                    crate::leanh::lean_dec(v_a_4355_);
                    crate::leanh::lean_dec_ref(v_snap_4351_);
                    crate::leanh::lean_dec_ref(v_params_4350_);
                    if v_isShared_4358_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4360_);
                        v___x_4364_ = v___x_4357_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4360_);
                        v___x_4364_ = v_reuseFailAlloc_4365_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4366_ = lean_nat_dec_le(v___x_4361_, v___x_4361_);
                    if v___x_4366_ == 0 {
                        if v___x_4362_ == 0 {
                            crate::leanh::lean_dec(v_a_4355_);
                            crate::leanh::lean_dec_ref(v_snap_4351_);
                            crate::leanh::lean_dec_ref(v_params_4350_);
                            if v_isShared_4358_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4360_);
                                v___x_4368_ = v___x_4357_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4369_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4360_);
                                v___x_4368_ = v_reuseFailAlloc_4369_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4357_);
                            v___x_4370_ = 0usize;
                            v___x_4371_ = lean_usize_of_nat(v___x_4361_);
                            v___x_4372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_4350_, v_snap_4351_, v_a_4355_, v___x_4370_, v___x_4371_, v___x_4360_, v___y_4352_);
                            crate::leanh::lean_dec(v_a_4355_);
                            return v___x_4372_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4357_);
                        v___x_4373_ = 0usize;
                        v___x_4374_ = lean_usize_of_nat(v___x_4361_);
                        v___x_4375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_handleCodeAction_spec__5(v_params_4350_, v_snap_4351_, v_a_4355_, v___x_4373_, v___x_4374_, v___x_4360_, v___y_4352_);
                        crate::leanh::lean_dec(v_a_4355_);
                        return v___x_4375_;
                    }
                }
            }
            2 => {
                return v___x_4364_;
            }
            3 => {
                return v___x_4368_;
            }
            4 => {
                if v_isShared_4380_ == 0 {
                    v___x_4382_ = v___x_4379_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
                    v___x_4382_ = v_reuseFailAlloc_4383_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__1___boxed(
    mut v___f_4385_: *mut crate::leanh::LeanObject,
    mut v_params_4386_: *mut crate::leanh::LeanObject,
    mut v_snap_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lean_Server_handleCodeAction___lam__1(
        v___f_4385_,
        v_params_4386_,
        v_snap_4387_,
        v___y_4388_,
    );
    crate::leanh::lean_dec_ref(v___y_4388_);
    return v_res_4390_;
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__2(
    mut v___x_4391_: *mut crate::leanh::LeanObject,
    mut v_s_4392_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    v___x_4393_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_4392_);
    v___x_4394_ = lean_nat_dec_le(v___x_4391_, v___x_4393_);
    crate::leanh::lean_dec(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__2___boxed(
    mut v___x_4395_: *mut crate::leanh::LeanObject,
    mut v_s_4396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4397_: u8 = 0;
    let mut v_r_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4397_ = l_Lean_Server_handleCodeAction___lam__2(v___x_4395_, v_s_4396_);
    crate::leanh::lean_dec_ref(v_s_4396_);
    crate::leanh::lean_dec(v___x_4395_);
    v_r_4398_ = crate::leanh::lean_box((v_res_4397_) as usize);
    return v_r_4398_;
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__3(
    mut v___x_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4399_);
    return v___x_4402_;
}
pub unsafe fn l_Lean_Server_handleCodeAction___lam__3___boxed(
    mut v___x_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4406_ = l_Lean_Server_handleCodeAction___lam__3(v___x_4403_, v___y_4404_);
    crate::leanh::lean_dec_ref(v___y_4404_);
    return v_res_4406_;
}
pub unsafe fn l_Lean_Server_handleCodeAction(
    mut v_params_4413_: *mut crate::leanh::LeanObject,
    mut v_a_4414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4416_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(v_a_4414_);
    v_a_4417_ = crate::leanh::lean_ctor_get(v___x_4416_, 0);
    crate::leanh::lean_inc(v_a_4417_);
    crate::leanh::lean_dec_ref(v___x_4416_);
    v_toEditableDocumentCore_4418_ = crate::leanh::lean_ctor_get(v_a_4417_, 0);
    v_meta_4419_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_4418_, 0);
    v_range_4420_ = crate::leanh::lean_ctor_get(v_params_4413_, 3);
    v_text_4421_ = crate::leanh::lean_ctor_get(v_meta_4419_, 3);
    v_end_4422_ = crate::leanh::lean_ctor_get(v_range_4420_, 1);
    crate::leanh::lean_inc_ref(v_end_4422_);
    v___f_4423_ = l_Lean_Server_handleCodeAction___closed__0;
    v___f_4424_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_handleCodeAction___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4424_, 0, v___f_4423_);
    crate::leanh::lean_closure_set(v___f_4424_, 1, v_params_4413_);
    v___x_4425_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4421_, v_end_4422_);
    v___f_4426_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_handleCodeAction___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4426_, 0, v___x_4425_);
    v___f_4427_ = l_Lean_Server_handleCodeAction___closed__2;
    v___x_4428_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(
        v_a_4417_,
        v___f_4426_,
        v___f_4427_,
        v___f_4424_,
        v_a_4414_,
    );
    return v___x_4428_;
}
pub unsafe fn l_Lean_Server_handleCodeAction___boxed(
    mut v_params_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
    mut v_a_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4432_ = l_Lean_Server_handleCodeAction(v_params_4429_, v_a_4430_);
    crate::leanh::lean_dec_ref(v_a_4430_);
    return v_res_4432_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0(
    mut v_params_4433_: *mut crate::leanh::LeanObject,
    mut v_fst_4434_: *mut crate::leanh::LeanObject,
    mut v_as_4435_: *mut crate::leanh::LeanObject,
    mut v_i_4436_: *mut crate::leanh::LeanObject,
    mut v_j_4437_: *mut crate::leanh::LeanObject,
    mut v_inv_4438_: *mut crate::leanh::LeanObject,
    mut v_bs_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___redArg(
        v_params_4433_,
        v_fst_4434_,
        v_as_4435_,
        v_i_4436_,
        v_j_4437_,
        v_bs_4439_,
    );
    return v___x_4442_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0___boxed(
    mut v_params_4443_: *mut crate::leanh::LeanObject,
    mut v_fst_4444_: *mut crate::leanh::LeanObject,
    mut v_as_4445_: *mut crate::leanh::LeanObject,
    mut v_i_4446_: *mut crate::leanh::LeanObject,
    mut v_j_4447_: *mut crate::leanh::LeanObject,
    mut v_inv_4448_: *mut crate::leanh::LeanObject,
    mut v_bs_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4452_ = l_Array_mapFinIdxM_map___at___00Lean_Server_handleCodeAction_spec__0(
        v_params_4443_,
        v_fst_4444_,
        v_as_4445_,
        v_i_4446_,
        v_j_4447_,
        v_inv_4448_,
        v_bs_4449_,
        v___y_4450_,
    );
    crate::leanh::lean_dec_ref(v___y_4450_);
    crate::leanh::lean_dec_ref(v_as_4445_);
    return v_res_4452_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1(
    mut v_init_4453_: *mut crate::leanh::LeanObject,
    mut v_t_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_handleCodeAction_spec__1_spec__1(v_init_4453_, v_t_4454_);
    return v___x_4455_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(
    mut v_00_u03b1_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4461_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___redArg();
    return v___x_4461_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v___y_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4467_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__6(v_00_u03b1_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
    crate::leanh::lean_dec(v___y_4465_);
    crate::leanh::lean_dec_ref(v___y_4464_);
    crate::leanh::lean_dec_ref(v___y_4463_);
    return v_res_4467_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(
    mut v_00_u03b1_4468_: *mut crate::leanh::LeanObject,
    mut v_typeName_4469_: *mut crate::leanh::LeanObject,
    mut v_constName_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
    mut v___y_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4475_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___redArg(v_typeName_4469_, v_constName_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
    return v___x_4475_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3___boxed(
    mut v_00_u03b1_4476_: *mut crate::leanh::LeanObject,
    mut v_typeName_4477_: *mut crate::leanh::LeanObject,
    mut v_constName_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4483_ = l_Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3(v_00_u03b1_4476_, v_typeName_4477_, v_constName_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
    crate::leanh::lean_dec(v___y_4481_);
    crate::leanh::lean_dec_ref(v___y_4480_);
    crate::leanh::lean_dec_ref(v___y_4479_);
    return v_res_4483_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(
    mut v_00_u03b1_4484_: *mut crate::leanh::LeanObject,
    mut v_x_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___redArg(v_x_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
    return v___x_4490_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_4491_: *mut crate::leanh::LeanObject,
    mut v_x_4492_: *mut crate::leanh::LeanObject,
    mut v___y_4493_: *mut crate::leanh::LeanObject,
    mut v___y_4494_: *mut crate::leanh::LeanObject,
    mut v___y_4495_: *mut crate::leanh::LeanObject,
    mut v___y_4496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4497_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5(v_00_u03b1_4491_, v_x_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
    crate::leanh::lean_dec(v___y_4495_);
    crate::leanh::lean_dec_ref(v___y_4494_);
    crate::leanh::lean_dec_ref(v___y_4493_);
    return v_res_4497_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(
    mut v_00_u03b1_4498_: *mut crate::leanh::LeanObject,
    mut v_msg_4499_: *mut crate::leanh::LeanObject,
    mut v___y_4500_: *mut crate::leanh::LeanObject,
    mut v___y_4501_: *mut crate::leanh::LeanObject,
    mut v___y_4502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4504_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___redArg(v_msg_4499_, v___y_4501_, v___y_4502_);
    return v___x_4504_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9___boxed(
    mut v_00_u03b1_4505_: *mut crate::leanh::LeanObject,
    mut v_msg_4506_: *mut crate::leanh::LeanObject,
    mut v___y_4507_: *mut crate::leanh::LeanObject,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4511_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2_spec__3_spec__5_spec__9(v_00_u03b1_4505_, v_msg_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
    crate::leanh::lean_dec(v___y_4509_);
    crate::leanh::lean_dec_ref(v___y_4508_);
    crate::leanh::lean_dec_ref(v___y_4507_);
    return v_res_4511_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(
    mut v_sz_4512_: usize,
    mut v_i_4513_: usize,
    mut v_bs_4514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4515_: u8 = 0;
    let mut v_v_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: usize = 0;
    let mut v___x_4521_: usize = 0;
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4515_ = lean_usize_dec_lt(v_i_4513_, v_sz_4512_);
                if v___x_4515_ == 0 {
                    return v_bs_4514_;
                } else {
                    v_v_4516_ = lean_array_uget(v_bs_4514_, v_i_4513_);
                    v___x_4517_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4518_ = lean_array_uset(v_bs_4514_, v_i_4513_, v___x_4517_);
                    v___x_4519_ = l_Lean_Lsp_instToJsonCodeAction_toJson(v_v_4516_);
                    v___x_4520_ = 1usize;
                    v___x_4521_ = lean_usize_add(v_i_4513_, v___x_4520_);
                    v___x_4522_ = lean_array_uset(v_bs_x27_4518_, v_i_4513_, v___x_4519_);
                    v_i_4513_ = v___x_4521_;
                    v_bs_4514_ = v___x_4522_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(
    mut v_sz_4524_: *mut crate::leanh::LeanObject,
    mut v_i_4525_: *mut crate::leanh::LeanObject,
    mut v_bs_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4527_: usize = 0;
    let mut v_i_boxed_4528_: usize = 0;
    let mut v_res_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4527_ = crate::leanh::lean_unbox_usize(v_sz_4524_);
    crate::leanh::lean_dec(v_sz_4524_);
    v_i_boxed_4528_ = crate::leanh::lean_unbox_usize(v_i_4525_);
    crate::leanh::lean_dec(v_i_4525_);
    v_res_4529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_sz_boxed_4527_, v_i_boxed_4528_, v_bs_4526_);
    return v_res_4529_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(
    mut v_a_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4531_: usize = 0;
    let mut v___x_4532_: usize = 0;
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4531_ = lean_array_size(v_a_4530_);
    v___x_4532_ = 0usize;
    v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_sz_4531_, v___x_4532_, v_a_4530_);
    v___x_4534_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4534_, 0, v___x_4533_);
    return v___x_4534_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(
    mut v_serialize_x3f_4535_: *mut crate::leanh::LeanObject,
    mut v_a_4536_: u8,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v_a_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v_val_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4557_: u8 = 0;
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_4537_) == 0 {
                    crate::leanh::lean_dec(v_serialize_x3f_4535_);
                    v_a_4538_ = crate::leanh::lean_ctor_get(v___y_4537_, 0);
                    v_isSharedCheck_4545_ = (!crate::leanh::lean_is_exclusive(v___y_4537_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4540_ = v___y_4537_;
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4538_);
                        crate::leanh::lean_dec(v___y_4537_);
                        v___x_4540_ = crate::leanh::lean_box(0);
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_serialize_x3f_4535_) == 1 {
                        v_a_4546_ = crate::leanh::lean_ctor_get(v___y_4537_, 0);
                        v_isSharedCheck_4557_ =
                            (!crate::leanh::lean_is_exclusive(v___y_4537_)) as u8;
                        if v_isSharedCheck_4557_ == 0 {
                            v___x_4548_ = v___y_4537_;
                            v_isShared_4549_ = v_isSharedCheck_4557_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4546_);
                            crate::leanh::lean_dec(v___y_4537_);
                            v___x_4548_ = crate::leanh::lean_box(0);
                            v_isShared_4549_ = v_isSharedCheck_4557_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_serialize_x3f_4535_);
                        v_a_4558_ = crate::leanh::lean_ctor_get(v___y_4537_, 0);
                        v_isSharedCheck_4569_ =
                            (!crate::leanh::lean_is_exclusive(v___y_4537_)) as u8;
                        if v_isSharedCheck_4569_ == 0 {
                            v___x_4560_ = v___y_4537_;
                            v_isShared_4561_ = v_isSharedCheck_4569_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4558_);
                            crate::leanh::lean_dec(v___y_4537_);
                            v___x_4560_ = crate::leanh::lean_box(0);
                            v_isShared_4561_ = v_isSharedCheck_4569_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4543_;
            }
            3 => {
                v_val_4550_ = crate::leanh::lean_ctor_get(v_serialize_x3f_4535_, 0);
                crate::leanh::lean_inc(v_val_4550_);
                crate::leanh::lean_dec_ref_known(v_serialize_x3f_4535_, 1);
                v___x_4551_ = crate::leanh::lean_box(0);
                v___x_4552_ = crate::leanh::lean_apply_1(v_val_4550_, v_a_4546_);
                v___x_4553_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4553_, 0, v___x_4551_);
                crate::leanh::lean_ctor_set(v___x_4553_, 1, v___x_4552_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4553_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_a_4536_,
                );
                if v_isShared_4549_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4548_, 0, v___x_4553_);
                    v___x_4555_ = v___x_4548_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
                    v___x_4555_ = v_reuseFailAlloc_4556_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4555_;
            }
            5 => {
                v___x_4562_ = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__2(v_a_4558_);
                crate::leanh::lean_inc(v___x_4562_);
                v___x_4563_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4563_, 0, v___x_4562_);
                v___x_4564_ = l_Lean_Json_compress(v___x_4562_);
                v___x_4565_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4565_, 0, v___x_4563_);
                crate::leanh::lean_ctor_set(v___x_4565_, 1, v___x_4564_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4565_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_a_4536_,
                );
                if v_isShared_4561_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4565_);
                    v___x_4567_ = v___x_4560_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
                    v___x_4567_ = v_reuseFailAlloc_4568_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v_serialize_x3f_4570_: *mut crate::leanh::LeanObject,
    mut v_a_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_828__boxed_4573_: u8 = 0;
    let mut v_res_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_828__boxed_4573_ = (crate::leanh::lean_unbox(v_a_4571_) as u8);
    v_res_4574_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4570_, v_a_828__boxed_4573_, v___y_4572_);
    return v_res_4574_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(
    mut v_keys_4575_: *mut crate::leanh::LeanObject,
    mut v_i_4576_: *mut crate::leanh::LeanObject,
    mut v_k_4577_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: u8 = 0;
    let mut v_k_x27_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4578_ = lean_array_get_size(v_keys_4575_);
                v___x_4579_ = lean_nat_dec_lt(v_i_4576_, v___x_4578_);
                if v___x_4579_ == 0 {
                    crate::leanh::lean_dec(v_i_4576_);
                    return v___x_4579_;
                } else {
                    v_k_x27_4580_ = lean_array_fget_borrowed(v_keys_4575_, v_i_4576_);
                    v___x_4581_ = lean_string_dec_eq(v_k_4577_, v_k_x27_4580_);
                    if v___x_4581_ == 0 {
                        v___x_4582_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4583_ = lean_nat_add(v_i_4576_, v___x_4582_);
                        crate::leanh::lean_dec(v_i_4576_);
                        v_i_4576_ = v___x_4583_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4576_);
                        return v___x_4581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg___boxed(
    mut v_keys_4585_: *mut crate::leanh::LeanObject,
    mut v_i_4586_: *mut crate::leanh::LeanObject,
    mut v_k_4587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4588_: u8 = 0;
    let mut v_r_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4588_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_keys_4585_, v_i_4586_, v_k_4587_);
    crate::leanh::lean_dec_ref(v_k_4587_);
    crate::leanh::lean_dec_ref(v_keys_4585_);
    v_r_4589_ = crate::leanh::lean_box((v_res_4588_) as usize);
    return v_r_4589_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_4590_: usize = 0;
    let mut v___x_4591_: usize = 0;
    let mut v___x_4592_: usize = 0;
    v___x_4590_ = 5usize;
    v___x_4591_ = 1usize;
    v___x_4592_ = lean_usize_shift_left(v___x_4591_, v___x_4590_);
    return v___x_4592_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_4593_: usize = 0;
    let mut v___x_4594_: usize = 0;
    let mut v___x_4595_: usize = 0;
    v___x_4593_ = 1usize;
    v___x_4594_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
    v___x_4595_ = lean_usize_sub(v___x_4594_, v___x_4593_);
    return v___x_4595_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(
    mut v_x_4596_: *mut crate::leanh::LeanObject,
    mut v_x_4597_: usize,
    mut v_x_4598_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: usize = 0;
    let mut v___x_4602_: usize = 0;
    let mut v___x_4603_: usize = 0;
    let mut v_j_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: u8 = 0;
    let mut v_node_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: usize = 0;
    let mut v___x_4611_: u8 = 0;
    let mut v_ks_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4596_) == 0 {
                    v_es_4599_ = crate::leanh::lean_ctor_get(v_x_4596_, 0);
                    v___x_4600_ = crate::leanh::lean_box(2);
                    v___x_4601_ = 5usize;
                    v___x_4602_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1);
                    v___x_4603_ = lean_usize_land(v_x_4597_, v___x_4602_);
                    v_j_4604_ = lean_usize_to_nat(v___x_4603_);
                    v___x_4605_ = lean_array_get_borrowed(v___x_4600_, v_es_4599_, v_j_4604_);
                    crate::leanh::lean_dec(v_j_4604_);
                    match crate::leanh::lean_obj_tag(v___x_4605_) {
                        0 => {
                            v_key_4606_ = crate::leanh::lean_ctor_get(v___x_4605_, 0);
                            v___x_4607_ = lean_string_dec_eq(v_x_4598_, v_key_4606_);
                            return v___x_4607_;
                        }
                        1 => {
                            v_node_4608_ = crate::leanh::lean_ctor_get(v___x_4605_, 0);
                            v___x_4609_ = lean_usize_shift_right(v_x_4597_, v___x_4601_);
                            v_x_4596_ = v_node_4608_;
                            v_x_4597_ = v___x_4609_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4611_ = 0;
                            return v___x_4611_;
                        }
                    }
                } else {
                    v_ks_4612_ = crate::leanh::lean_ctor_get(v_x_4596_, 0);
                    v___x_4613_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4614_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_ks_4612_, v___x_4613_, v_x_4598_);
                    return v___x_4614_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(
    mut v_x_4615_: *mut crate::leanh::LeanObject,
    mut v_x_4616_: *mut crate::leanh::LeanObject,
    mut v_x_4617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_923__boxed_4618_: usize = 0;
    let mut v_res_4619_: u8 = 0;
    let mut v_r_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_923__boxed_4618_ = crate::leanh::lean_unbox_usize(v_x_4616_);
    crate::leanh::lean_dec(v_x_4616_);
    v_res_4619_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4615_, v_x_923__boxed_4618_, v_x_4617_);
    crate::leanh::lean_dec_ref(v_x_4617_);
    crate::leanh::lean_dec_ref(v_x_4615_);
    v_r_4620_ = crate::leanh::lean_box((v_res_4619_) as usize);
    return v_r_4620_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(
    mut v_x_4621_: *mut crate::leanh::LeanObject,
    mut v_x_4622_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4623_: u64 = 0;
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: u8 = 0;
    v___x_4623_ = lean_string_hash(v_x_4622_);
    v___x_4624_ = lean_uint64_to_usize(v___x_4623_);
    v___x_4625_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4621_, v___x_4624_, v_x_4622_);
    return v___x_4625_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg___boxed(
    mut v_x_4626_: *mut crate::leanh::LeanObject,
    mut v_x_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4628_: u8 = 0;
    let mut v_r_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4628_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4626_, v_x_4627_);
    crate::leanh::lean_dec_ref(v_x_4627_);
    crate::leanh::lean_dec_ref(v_x_4626_);
    v_r_4629_ = crate::leanh::lean_box((v_res_4628_) as usize);
    return v_r_4629_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(
    mut v_x_4630_: *mut crate::leanh::LeanObject,
    mut v_x_4631_: *mut crate::leanh::LeanObject,
    mut v_x_4632_: *mut crate::leanh::LeanObject,
    mut v_x_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: u8 = 0;
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4634_ = crate::leanh::lean_ctor_get(v_x_4630_, 0);
                v_vs_4635_ = crate::leanh::lean_ctor_get(v_x_4630_, 1);
                v_isSharedCheck_4659_ = (!crate::leanh::lean_is_exclusive(v_x_4630_)) as u8;
                if v_isSharedCheck_4659_ == 0 {
                    v___x_4637_ = v_x_4630_;
                    v_isShared_4638_ = v_isSharedCheck_4659_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4635_);
                    crate::leanh::lean_inc(v_ks_4634_);
                    crate::leanh::lean_dec(v_x_4630_);
                    v___x_4637_ = crate::leanh::lean_box(0);
                    v_isShared_4638_ = v_isSharedCheck_4659_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4639_ = lean_array_get_size(v_ks_4634_);
                v___x_4640_ = lean_nat_dec_lt(v_x_4631_, v___x_4639_);
                if v___x_4640_ == 0 {
                    crate::leanh::lean_dec(v_x_4631_);
                    v___x_4641_ = lean_array_push(v_ks_4634_, v_x_4632_);
                    v___x_4642_ = lean_array_push(v_vs_4635_, v_x_4633_);
                    if v_isShared_4638_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4637_, 1, v___x_4642_);
                        crate::leanh::lean_ctor_set(v___x_4637_, 0, v___x_4641_);
                        v___x_4644_ = v___x_4637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4645_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4641_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4642_);
                        v___x_4644_ = v_reuseFailAlloc_4645_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4646_ = lean_array_fget_borrowed(v_ks_4634_, v_x_4631_);
                    v___x_4647_ = lean_string_dec_eq(v_x_4632_, v_k_x27_4646_);
                    if v___x_4647_ == 0 {
                        if v_isShared_4638_ == 0 {
                            v___x_4649_ = v___x_4637_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4653_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_ks_4634_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 1, v_vs_4635_);
                            v___x_4649_ = v_reuseFailAlloc_4653_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4654_ = lean_array_fset(v_ks_4634_, v_x_4631_, v_x_4632_);
                        v___x_4655_ = lean_array_fset(v_vs_4635_, v_x_4631_, v_x_4633_);
                        crate::leanh::lean_dec(v_x_4631_);
                        if v_isShared_4638_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4637_, 1, v___x_4655_);
                            crate::leanh::lean_ctor_set(v___x_4637_, 0, v___x_4654_);
                            v___x_4657_ = v___x_4637_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4658_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4654_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4658_, 1, v___x_4655_);
                            v___x_4657_ = v_reuseFailAlloc_4658_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4644_;
            }
            3 => {
                v___x_4650_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4651_ = lean_nat_add(v_x_4631_, v___x_4650_);
                crate::leanh::lean_dec(v_x_4631_);
                v_x_4630_ = v___x_4649_;
                v_x_4631_ = v___x_4651_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(
    mut v_n_4660_: *mut crate::leanh::LeanObject,
    mut v_k_4661_: *mut crate::leanh::LeanObject,
    mut v_v_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4664_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(v_n_4660_, v___x_4663_, v_k_4661_, v_v_4662_);
    return v___x_4664_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4665_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(
    mut v_x_4666_: *mut crate::leanh::LeanObject,
    mut v_x_4667_: usize,
    mut v_x_4668_: usize,
    mut v_x_4669_: *mut crate::leanh::LeanObject,
    mut v_x_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: usize = 0;
    let mut v___x_4673_: usize = 0;
    let mut v___x_4674_: usize = 0;
    let mut v___x_4675_: usize = 0;
    let mut v_j_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: u8 = 0;
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v_v_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v_node_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4707_: usize = 0;
    let mut v___x_4708_: usize = 0;
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4713_: u8 = 0;
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_unused_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4721_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4726_: u8 = 0;
    let mut v_ks_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: usize = 0;
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: u8 = 0;
    let mut v_reuseFailAlloc_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4666_) == 0 {
                    v_es_4671_ = crate::leanh::lean_ctor_get(v_x_4666_, 0);
                    v___x_4672_ = 5usize;
                    v___x_4673_ = 1usize;
                    v___x_4674_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__1);
                    v___x_4675_ = lean_usize_land(v_x_4667_, v___x_4674_);
                    v_j_4676_ = lean_usize_to_nat(v___x_4675_);
                    v___x_4677_ = lean_array_get_size(v_es_4671_);
                    v___x_4678_ = lean_nat_dec_lt(v_j_4676_, v___x_4677_);
                    if v___x_4678_ == 0 {
                        crate::leanh::lean_dec(v_j_4676_);
                        crate::leanh::lean_dec(v_x_4670_);
                        crate::leanh::lean_dec_ref(v_x_4669_);
                        return v_x_4666_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4671_);
                        v_isSharedCheck_4715_ = (!crate::leanh::lean_is_exclusive(v_x_4666_)) as u8;
                        if v_isSharedCheck_4715_ == 0 {
                            v_unused_4716_ = crate::leanh::lean_ctor_get(v_x_4666_, 0);
                            crate::leanh::lean_dec(v_unused_4716_);
                            v___x_4680_ = v_x_4666_;
                            v_isShared_4681_ = v_isSharedCheck_4715_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4666_);
                            v___x_4680_ = crate::leanh::lean_box(0);
                            v_isShared_4681_ = v_isSharedCheck_4715_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4717_ = crate::leanh::lean_ctor_get(v_x_4666_, 0);
                    v_vs_4718_ = crate::leanh::lean_ctor_get(v_x_4666_, 1);
                    v_isSharedCheck_4738_ = (!crate::leanh::lean_is_exclusive(v_x_4666_)) as u8;
                    if v_isSharedCheck_4738_ == 0 {
                        v___x_4720_ = v_x_4666_;
                        v_isShared_4721_ = v_isSharedCheck_4738_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4718_);
                        crate::leanh::lean_inc(v_ks_4717_);
                        crate::leanh::lean_dec(v_x_4666_);
                        v___x_4720_ = crate::leanh::lean_box(0);
                        v_isShared_4721_ = v_isSharedCheck_4738_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4682_ = lean_array_fget(v_es_4671_, v_j_4676_);
                v___x_4683_ = crate::leanh::lean_box(0);
                v_xs_x27_4684_ = lean_array_fset(v_es_4671_, v_j_4676_, v___x_4683_);
                match crate::leanh::lean_obj_tag(v_v_4682_) {
                    0 => {
                        v_key_4691_ = crate::leanh::lean_ctor_get(v_v_4682_, 0);
                        v_val_4692_ = crate::leanh::lean_ctor_get(v_v_4682_, 1);
                        v_isSharedCheck_4702_ = (!crate::leanh::lean_is_exclusive(v_v_4682_)) as u8;
                        if v_isSharedCheck_4702_ == 0 {
                            v___x_4694_ = v_v_4682_;
                            v_isShared_4695_ = v_isSharedCheck_4702_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4692_);
                            crate::leanh::lean_inc(v_key_4691_);
                            crate::leanh::lean_dec(v_v_4682_);
                            v___x_4694_ = crate::leanh::lean_box(0);
                            v_isShared_4695_ = v_isSharedCheck_4702_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4703_ = crate::leanh::lean_ctor_get(v_v_4682_, 0);
                        v_isSharedCheck_4713_ = (!crate::leanh::lean_is_exclusive(v_v_4682_)) as u8;
                        if v_isSharedCheck_4713_ == 0 {
                            v___x_4705_ = v_v_4682_;
                            v_isShared_4706_ = v_isSharedCheck_4713_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4703_);
                            crate::leanh::lean_dec(v_v_4682_);
                            v___x_4705_ = crate::leanh::lean_box(0);
                            v_isShared_4706_ = v_isSharedCheck_4713_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4714_, 0, v_x_4669_);
                        crate::leanh::lean_ctor_set(v___x_4714_, 1, v_x_4670_);
                        v___y_4686_ = v___x_4714_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4687_ = lean_array_fset(v_xs_x27_4684_, v_j_4676_, v___y_4686_);
                crate::leanh::lean_dec(v_j_4676_);
                if v_isShared_4681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4687_);
                    v___x_4689_ = v___x_4680_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
                    v___x_4689_ = v_reuseFailAlloc_4690_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4689_;
            }
            4 => {
                v___x_4696_ = lean_string_dec_eq(v_x_4669_, v_key_4691_);
                if v___x_4696_ == 0 {
                    crate::leanh::lean_del_object(v___x_4694_);
                    v___x_4697_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4691_,
                        v_val_4692_,
                        v_x_4669_,
                        v_x_4670_,
                    );
                    v___x_4698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4698_, 0, v___x_4697_);
                    v___y_4686_ = v___x_4698_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4692_);
                    crate::leanh::lean_dec(v_key_4691_);
                    if v_isShared_4695_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4694_, 1, v_x_4670_);
                        crate::leanh::lean_ctor_set(v___x_4694_, 0, v_x_4669_);
                        v___x_4700_ = v___x_4694_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4701_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_x_4669_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_x_4670_);
                        v___x_4700_ = v_reuseFailAlloc_4701_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4686_ = v___x_4700_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4707_ = lean_usize_shift_right(v_x_4667_, v___x_4672_);
                v___x_4708_ = lean_usize_add(v_x_4668_, v___x_4673_);
                v___x_4709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_node_4703_, v___x_4707_, v___x_4708_, v_x_4669_, v_x_4670_);
                if v_isShared_4706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4705_, 0, v___x_4709_);
                    v___x_4711_ = v___x_4705_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
                    v___x_4711_ = v_reuseFailAlloc_4712_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4686_ = v___x_4711_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4721_ == 0 {
                    v___x_4723_ = v___x_4720_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4737_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_ks_4717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_vs_4718_);
                    v___x_4723_ = v_reuseFailAlloc_4737_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4724_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(v___x_4723_, v_x_4669_, v_x_4670_);
                v___x_4732_ = 7usize;
                v___x_4733_ = lean_usize_dec_le(v___x_4732_, v_x_4668_);
                if v___x_4733_ == 0 {
                    v___x_4734_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4724_);
                    v___x_4735_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4736_ = lean_nat_dec_lt(v___x_4734_, v___x_4735_);
                    crate::leanh::lean_dec(v___x_4734_);
                    v___y_4726_ = v___x_4736_;
                    state = 10;
                    continue;
                } else {
                    v___y_4726_ = v___x_4733_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4726_ == 0 {
                    v_ks_4727_ = crate::leanh::lean_ctor_get(v_newNode_4724_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4727_);
                    v_vs_4728_ = crate::leanh::lean_ctor_get(v_newNode_4724_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4728_);
                    crate::leanh::lean_dec_ref(v_newNode_4724_);
                    v___x_4729_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4730_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___closed__0);
                    v___x_4731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_x_4668_, v_ks_4727_, v_vs_4728_, v___x_4729_, v___x_4730_);
                    crate::leanh::lean_dec_ref(v_vs_4728_);
                    crate::leanh::lean_dec_ref(v_ks_4727_);
                    return v___x_4731_;
                } else {
                    return v_newNode_4724_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(
    mut v_depth_4739_: usize,
    mut v_keys_4740_: *mut crate::leanh::LeanObject,
    mut v_vals_4741_: *mut crate::leanh::LeanObject,
    mut v_i_4742_: *mut crate::leanh::LeanObject,
    mut v_entries_4743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: u8 = 0;
    let mut v_k_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u64 = 0;
    let mut v_h_4749_: usize = 0;
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: usize = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v_h_4755_: usize = 0;
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4744_ = lean_array_get_size(v_keys_4740_);
                v___x_4745_ = lean_nat_dec_lt(v_i_4742_, v___x_4744_);
                if v___x_4745_ == 0 {
                    crate::leanh::lean_dec(v_i_4742_);
                    return v_entries_4743_;
                } else {
                    v_k_4746_ = lean_array_fget_borrowed(v_keys_4740_, v_i_4742_);
                    v_v_4747_ = lean_array_fget_borrowed(v_vals_4741_, v_i_4742_);
                    v___x_4748_ = lean_string_hash(v_k_4746_);
                    v_h_4749_ = lean_uint64_to_usize(v___x_4748_);
                    v___x_4750_ = 5usize;
                    v___x_4751_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4752_ = 1usize;
                    v___x_4753_ = lean_usize_sub(v_depth_4739_, v___x_4752_);
                    v___x_4754_ = lean_usize_mul(v___x_4750_, v___x_4753_);
                    v_h_4755_ = lean_usize_shift_right(v_h_4749_, v___x_4754_);
                    v___x_4756_ = lean_nat_add(v_i_4742_, v___x_4751_);
                    crate::leanh::lean_dec(v_i_4742_);
                    crate::leanh::lean_inc(v_v_4747_);
                    crate::leanh::lean_inc(v_k_4746_);
                    v___x_4757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_entries_4743_, v_h_4755_, v_depth_4739_, v_k_4746_, v_v_4747_);
                    v_i_4742_ = v___x_4756_;
                    v_entries_4743_ = v___x_4757_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg___boxed(
    mut v_depth_4759_: *mut crate::leanh::LeanObject,
    mut v_keys_4760_: *mut crate::leanh::LeanObject,
    mut v_vals_4761_: *mut crate::leanh::LeanObject,
    mut v_i_4762_: *mut crate::leanh::LeanObject,
    mut v_entries_4763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4764_: usize = 0;
    let mut v_res_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4764_ = crate::leanh::lean_unbox_usize(v_depth_4759_);
    crate::leanh::lean_dec(v_depth_4759_);
    v_res_4765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_depth_boxed_4764_, v_keys_4760_, v_vals_4761_, v_i_4762_, v_entries_4763_);
    crate::leanh::lean_dec_ref(v_vals_4761_);
    crate::leanh::lean_dec_ref(v_keys_4760_);
    return v_res_4765_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg___boxed(
    mut v_x_4766_: *mut crate::leanh::LeanObject,
    mut v_x_4767_: *mut crate::leanh::LeanObject,
    mut v_x_4768_: *mut crate::leanh::LeanObject,
    mut v_x_4769_: *mut crate::leanh::LeanObject,
    mut v_x_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1064__boxed_4771_: usize = 0;
    let mut v_x_1065__boxed_4772_: usize = 0;
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1064__boxed_4771_ = crate::leanh::lean_unbox_usize(v_x_4767_);
    crate::leanh::lean_dec(v_x_4767_);
    v_x_1065__boxed_4772_ = crate::leanh::lean_unbox_usize(v_x_4768_);
    crate::leanh::lean_dec(v_x_4768_);
    v_res_4773_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_4766_, v_x_1064__boxed_4771_, v_x_1065__boxed_4772_, v_x_4769_, v_x_4770_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(
    mut v_x_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
    mut v_x_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4777_: u64 = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4777_ = lean_string_hash(v_x_4775_);
    v___x_4778_ = lean_uint64_to_usize(v___x_4777_);
    v___x_4779_ = 1usize;
    v___x_4780_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_4774_, v___x_4778_, v___x_4779_, v_x_4775_, v_x_4776_);
    return v___x_4780_;
}
pub unsafe fn l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(
    mut v_params_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4788_: u8 = 0;
    let mut v___x_4789_: u8 = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v_a_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4804_: u8 = 0;
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_params_4783_);
                v___x_4784_ = l_Lean_Lsp_instFromJsonCodeActionParams_fromJson(v_params_4783_);
                if crate::leanh::lean_obj_tag(v___x_4784_) == 0 {
                    v_a_4785_ = crate::leanh::lean_ctor_get(v___x_4784_, 0);
                    v_isSharedCheck_4800_ = (!crate::leanh::lean_is_exclusive(v___x_4784_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4787_ = v___x_4784_;
                        v_isShared_4788_ = v_isSharedCheck_4800_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4785_);
                        crate::leanh::lean_dec(v___x_4784_);
                        v___x_4787_ = crate::leanh::lean_box(0);
                        v_isShared_4788_ = v_isSharedCheck_4800_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_params_4783_);
                    v_a_4801_ = crate::leanh::lean_ctor_get(v___x_4784_, 0);
                    v_isSharedCheck_4808_ = (!crate::leanh::lean_is_exclusive(v___x_4784_)) as u8;
                    if v_isSharedCheck_4808_ == 0 {
                        v___x_4803_ = v___x_4784_;
                        v_isShared_4804_ = v_isSharedCheck_4808_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4801_);
                        crate::leanh::lean_dec(v___x_4784_);
                        v___x_4803_ = crate::leanh::lean_box(0);
                        v_isShared_4804_ = v_isSharedCheck_4808_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4789_ = 3;
                v___x_4790_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0;
                v___x_4791_ = l_Lean_Json_compress(v_params_4783_);
                v___x_4792_ = lean_string_append(v___x_4790_, v___x_4791_);
                crate::leanh::lean_dec_ref(v___x_4791_);
                v___x_4793_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1;
                v___x_4794_ = lean_string_append(v___x_4792_, v___x_4793_);
                v___x_4795_ = lean_string_append(v___x_4794_, v_a_4785_);
                crate::leanh::lean_dec(v_a_4785_);
                v___x_4796_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4796_, 0, v___x_4795_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4796_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4789_,
                );
                if v_isShared_4788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4787_, 0, v___x_4796_);
                    v___x_4798_ = v___x_4787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
                    v___x_4798_ = v_reuseFailAlloc_4799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4798_;
            }
            3 => {
                if v_isShared_4804_ == 0 {
                    v___x_4806_ = v___x_4803_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
                    v___x_4806_ = v_reuseFailAlloc_4807_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_params_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4815_: u8 = 0;
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut v_a_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4823_: u8 = 0;
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4811_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(v_params_4809_);
                if crate::leanh::lean_obj_tag(v___x_4811_) == 0 {
                    v_a_4812_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
                    v_isSharedCheck_4819_ = (!crate::leanh::lean_is_exclusive(v___x_4811_)) as u8;
                    if v_isSharedCheck_4819_ == 0 {
                        v___x_4814_ = v___x_4811_;
                        v_isShared_4815_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4812_);
                        crate::leanh::lean_dec(v___x_4811_);
                        v___x_4814_ = crate::leanh::lean_box(0);
                        v_isShared_4815_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4820_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
                    v_isSharedCheck_4827_ = (!crate::leanh::lean_is_exclusive(v___x_4811_)) as u8;
                    if v_isSharedCheck_4827_ == 0 {
                        v___x_4822_ = v___x_4811_;
                        v_isShared_4823_ = v_isSharedCheck_4827_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4820_);
                        crate::leanh::lean_dec(v___x_4811_);
                        v___x_4822_ = crate::leanh::lean_box(0);
                        v_isShared_4823_ = v_isSharedCheck_4827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4815_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4814_, 1);
                    v___x_4817_ = v___x_4814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
                    v___x_4817_ = v_reuseFailAlloc_4818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4817_;
            }
            3 => {
                if v_isShared_4823_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4822_, 0);
                    v___x_4825_ = v___x_4822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
                    v___x_4825_ = v_reuseFailAlloc_4826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_params_4828_: *mut crate::leanh::LeanObject,
    mut v_a_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4830_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4828_);
    return v_res_4830_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(
    mut v_handler_4831_: *mut crate::leanh::LeanObject,
    mut v___f_4832_: *mut crate::leanh::LeanObject,
    mut v_j_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4847_: u8 = 0;
    let mut v_a_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4855_: u8 = 0;
    let mut v_a_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4859_: u8 = 0;
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4836_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4833_);
                if crate::leanh::lean_obj_tag(v___x_4836_) == 0 {
                    v_a_4837_ = crate::leanh::lean_ctor_get(v___x_4836_, 0);
                    crate::leanh::lean_inc(v_a_4837_);
                    crate::leanh::lean_dec_ref_known(v___x_4836_, 1);
                    crate::leanh::lean_inc_ref(v___y_4834_);
                    v___x_4838_ = crate::leanh::lean_apply_3(
                        v_handler_4831_,
                        v_a_4837_,
                        v___y_4834_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4838_) == 0 {
                        v_a_4839_ = crate::leanh::lean_ctor_get(v___x_4838_, 0);
                        v_isSharedCheck_4847_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4838_)) as u8;
                        if v_isSharedCheck_4847_ == 0 {
                            v___x_4841_ = v___x_4838_;
                            v_isShared_4842_ = v_isSharedCheck_4847_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4839_);
                            crate::leanh::lean_dec(v___x_4838_);
                            v___x_4841_ = crate::leanh::lean_box(0);
                            v_isShared_4842_ = v_isSharedCheck_4847_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_4832_);
                        v_a_4848_ = crate::leanh::lean_ctor_get(v___x_4838_, 0);
                        v_isSharedCheck_4855_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4838_)) as u8;
                        if v_isSharedCheck_4855_ == 0 {
                            v___x_4850_ = v___x_4838_;
                            v_isShared_4851_ = v_isSharedCheck_4855_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4848_);
                            crate::leanh::lean_dec(v___x_4838_);
                            v___x_4850_ = crate::leanh::lean_box(0);
                            v_isShared_4851_ = v_isSharedCheck_4855_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_4832_);
                    crate::leanh::lean_dec_ref(v_handler_4831_);
                    v_a_4856_ = crate::leanh::lean_ctor_get(v___x_4836_, 0);
                    v_isSharedCheck_4863_ = (!crate::leanh::lean_is_exclusive(v___x_4836_)) as u8;
                    if v_isSharedCheck_4863_ == 0 {
                        v___x_4858_ = v___x_4836_;
                        v_isShared_4859_ = v_isSharedCheck_4863_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4856_);
                        crate::leanh::lean_dec(v___x_4836_);
                        v___x_4858_ = crate::leanh::lean_box(0);
                        v_isShared_4859_ = v_isSharedCheck_4863_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4843_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4832_, v_a_4839_);
                if v_isShared_4842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4841_, 0, v___x_4843_);
                    v___x_4845_ = v___x_4841_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4843_);
                    v___x_4845_ = v_reuseFailAlloc_4846_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4845_;
            }
            3 => {
                if v_isShared_4851_ == 0 {
                    v___x_4853_ = v___x_4850_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
                    v___x_4853_ = v_reuseFailAlloc_4854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4853_;
            }
            5 => {
                if v_isShared_4859_ == 0 {
                    v___x_4861_ = v___x_4858_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4862_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
                    v___x_4861_ = v_reuseFailAlloc_4862_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed(
    mut v_handler_4864_: *mut crate::leanh::LeanObject,
    mut v___f_4865_: *mut crate::leanh::LeanObject,
    mut v_j_4866_: *mut crate::leanh::LeanObject,
    mut v___y_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4869_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2(v_handler_4864_, v___f_4865_, v_j_4866_, v___y_4867_);
    crate::leanh::lean_dec_ref(v___y_4867_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__0(
    mut v_j_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_a_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v_textDocument_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4871_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0(v_j_4870_);
                if crate::leanh::lean_obj_tag(v___x_4871_) == 0 {
                    v_a_4872_ = crate::leanh::lean_ctor_get(v___x_4871_, 0);
                    v_isSharedCheck_4879_ = (!crate::leanh::lean_is_exclusive(v___x_4871_)) as u8;
                    if v_isSharedCheck_4879_ == 0 {
                        v___x_4874_ = v___x_4871_;
                        v_isShared_4875_ = v_isSharedCheck_4879_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4872_);
                        crate::leanh::lean_dec(v___x_4871_);
                        v___x_4874_ = crate::leanh::lean_box(0);
                        v_isShared_4875_ = v_isSharedCheck_4879_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4880_ = crate::leanh::lean_ctor_get(v___x_4871_, 0);
                    v_isSharedCheck_4888_ = (!crate::leanh::lean_is_exclusive(v___x_4871_)) as u8;
                    if v_isSharedCheck_4888_ == 0 {
                        v___x_4882_ = v___x_4871_;
                        v_isShared_4883_ = v_isSharedCheck_4888_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4880_);
                        crate::leanh::lean_dec(v___x_4871_);
                        v___x_4882_ = crate::leanh::lean_box(0);
                        v_isShared_4883_ = v_isSharedCheck_4888_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4875_ == 0 {
                    v___x_4877_ = v___x_4874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4877_;
            }
            3 => {
                v_textDocument_4884_ = crate::leanh::lean_ctor_get(v_a_4880_, 2);
                crate::leanh::lean_inc_ref(v_textDocument_4884_);
                crate::leanh::lean_dec(v_a_4880_);
                if v_isShared_4883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4882_, 0, v_textDocument_4884_);
                    v___x_4886_ = v___x_4882_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_textDocument_4884_);
                    v___x_4886_ = v_reuseFailAlloc_4887_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(
    mut v_method_4893_: *mut crate::leanh::LeanObject,
    mut v_handler_4894_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_4895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4901_: u8 = 0;
    let mut v___x_4902_: u8 = 0;
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4932_: u8 = 0;
    let mut v_a_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4897_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_4897_) == 0 {
                    v_a_4898_ = crate::leanh::lean_ctor_get(v___x_4897_, 0);
                    v_isSharedCheck_4932_ = (!crate::leanh::lean_is_exclusive(v___x_4897_)) as u8;
                    if v_isSharedCheck_4932_ == 0 {
                        v___x_4900_ = v___x_4897_;
                        v_isShared_4901_ = v_isSharedCheck_4932_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4898_);
                        crate::leanh::lean_dec(v___x_4897_);
                        v___x_4900_ = crate::leanh::lean_box(0);
                        v_isShared_4901_ = v_isSharedCheck_4932_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_serialize_x3f_4895_);
                    crate::leanh::lean_dec_ref(v_handler_4894_);
                    crate::leanh::lean_dec_ref(v_method_4893_);
                    v_a_4933_ = crate::leanh::lean_ctor_get(v___x_4897_, 0);
                    v_isSharedCheck_4940_ = (!crate::leanh::lean_is_exclusive(v___x_4897_)) as u8;
                    if v_isSharedCheck_4940_ == 0 {
                        v___x_4935_ = v___x_4897_;
                        v_isShared_4936_ = v_isSharedCheck_4940_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4933_);
                        crate::leanh::lean_dec(v___x_4897_);
                        v___x_4935_ = crate::leanh::lean_box(0);
                        v_isShared_4936_ = v_isSharedCheck_4940_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4902_ = (crate::leanh::lean_unbox(v_a_4898_) as u8);
                if v___x_4902_ == 0 {
                    crate::leanh::lean_dec(v_a_4898_);
                    crate::leanh::lean_dec(v_serialize_x3f_4895_);
                    crate::leanh::lean_dec_ref(v_handler_4894_);
                    v___x_4903_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0;
                    v___x_4904_ = lean_string_append(v___x_4903_, v_method_4893_);
                    crate::leanh::lean_dec_ref(v_method_4893_);
                    v___x_4905_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1;
                    v___x_4906_ = lean_string_append(v___x_4904_, v___x_4905_);
                    v___x_4907_ = lean_mk_io_user_error(v___x_4906_);
                    if v_isShared_4901_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4900_, 1);
                        crate::leanh::lean_ctor_set(v___x_4900_, 0, v___x_4907_);
                        v___x_4909_ = v___x_4900_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4907_);
                        v___x_4909_ = v_reuseFailAlloc_4910_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4911_ = l_Lean_Server_requestHandlers;
                    v___x_4912_ = lean_st_ref_get(v___x_4911_);
                    v___x_4913_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4912_, v_method_4893_);
                    crate::leanh::lean_dec(v___x_4912_);
                    if v___x_4913_ == 0 {
                        v___x_4914_ = lean_st_ref_take(v___x_4911_);
                        v___f_4915_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__2;
                        v___f_4916_ = crate::leanh::lean_alloc_closure(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_4916_, 0, v_serialize_x3f_4895_);
                        crate::leanh::lean_closure_set(v___f_4916_, 1, v_a_4898_);
                        v___f_4917_ = crate::leanh::lean_alloc_closure(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___lam__2___boxed as *mut core::ffi::c_void, 5, 2);
                        crate::leanh::lean_closure_set(v___f_4917_, 0, v_handler_4894_);
                        crate::leanh::lean_closure_set(v___f_4917_, 1, v___f_4916_);
                        v___x_4918_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4918_, 0, v___f_4915_);
                        crate::leanh::lean_ctor_set(v___x_4918_, 1, v___f_4917_);
                        v___x_4919_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v___x_4914_, v_method_4893_, v___x_4918_);
                        v___x_4920_ = lean_st_ref_set(v___x_4911_, v___x_4919_);
                        if v_isShared_4901_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4900_, 0, v___x_4920_);
                            v___x_4922_ = v___x_4900_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4923_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4920_);
                            v___x_4922_ = v_reuseFailAlloc_4923_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4898_);
                        crate::leanh::lean_dec(v_serialize_x3f_4895_);
                        crate::leanh::lean_dec_ref(v_handler_4894_);
                        v___x_4924_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0;
                        v___x_4925_ = lean_string_append(v___x_4924_, v_method_4893_);
                        crate::leanh::lean_dec_ref(v_method_4893_);
                        v___x_4926_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3;
                        v___x_4927_ = lean_string_append(v___x_4925_, v___x_4926_);
                        v___x_4928_ = lean_mk_io_user_error(v___x_4927_);
                        if v_isShared_4901_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4900_, 1);
                            crate::leanh::lean_ctor_set(v___x_4900_, 0, v___x_4928_);
                            v___x_4930_ = v___x_4900_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4931_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4928_);
                            v___x_4930_ = v_reuseFailAlloc_4931_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4909_;
            }
            3 => {
                return v___x_4922_;
            }
            4 => {
                return v___x_4930_;
            }
            5 => {
                if v_isShared_4936_ == 0 {
                    v___x_4938_ = v___x_4935_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
                    v___x_4938_ = v_reuseFailAlloc_4939_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___boxed(
    mut v_method_4941_: *mut crate::leanh::LeanObject,
    mut v_handler_4942_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_4943_: *mut crate::leanh::LeanObject,
    mut v_a_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(v_method_4941_, v_handler_4942_, v_serialize_x3f_4943_);
    return v_res_4945_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4949_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_;
    v___x_4950_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_;
    v___x_4951_ = crate::leanh::lean_box(0);
    v___x_4952_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0(v___x_4949_, v___x_4950_, v___x_4951_);
    return v___x_4952_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2____boxed(
    mut v_a_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4954_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_();
    return v_res_4954_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(
    mut v_params_4955_: *mut crate::leanh::LeanObject,
    mut v_a_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4958_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4955_);
    return v___x_4958_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_params_4959_: *mut crate::leanh::LeanObject,
    mut v_a_4960_: *mut crate::leanh::LeanObject,
    mut v_a_4961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4962_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__1(v_params_4959_, v_a_4960_);
    crate::leanh::lean_dec_ref(v_a_4960_);
    return v_res_4962_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(
    mut v_00_u03b2_4963_: *mut crate::leanh::LeanObject,
    mut v_x_4964_: *mut crate::leanh::LeanObject,
    mut v_x_4965_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4966_: u8 = 0;
    v___x_4966_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4964_, v_x_4965_);
    return v___x_4966_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___boxed(
    mut v_00_u03b2_4967_: *mut crate::leanh::LeanObject,
    mut v_x_4968_: *mut crate::leanh::LeanObject,
    mut v_x_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4970_: u8 = 0;
    let mut v_r_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3(v_00_u03b2_4967_, v_x_4968_, v_x_4969_);
    crate::leanh::lean_dec_ref(v_x_4969_);
    crate::leanh::lean_dec_ref(v_x_4968_);
    v_r_4971_ = crate::leanh::lean_box((v_res_4970_) as usize);
    return v_r_4971_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4(
    mut v_00_u03b2_4972_: *mut crate::leanh::LeanObject,
    mut v_x_4973_: *mut crate::leanh::LeanObject,
    mut v_x_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4976_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v_x_4973_, v_x_4974_, v_x_4975_);
    return v___x_4976_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(
    mut v_00_u03b2_4977_: *mut crate::leanh::LeanObject,
    mut v_x_4978_: *mut crate::leanh::LeanObject,
    mut v_x_4979_: usize,
    mut v_x_4980_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4981_: u8 = 0;
    v___x_4981_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4978_, v_x_4979_, v_x_4980_);
    return v___x_4981_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(
    mut v_00_u03b2_4982_: *mut crate::leanh::LeanObject,
    mut v_x_4983_: *mut crate::leanh::LeanObject,
    mut v_x_4984_: *mut crate::leanh::LeanObject,
    mut v_x_4985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1568__boxed_4986_: usize = 0;
    let mut v_res_4987_: u8 = 0;
    let mut v_r_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1568__boxed_4986_ = crate::leanh::lean_unbox_usize(v_x_4984_);
    crate::leanh::lean_dec(v_x_4984_);
    v_res_4987_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4982_, v_x_4983_, v_x_1568__boxed_4986_, v_x_4985_);
    crate::leanh::lean_dec_ref(v_x_4985_);
    crate::leanh::lean_dec_ref(v_x_4983_);
    v_r_4988_ = crate::leanh::lean_box((v_res_4987_) as usize);
    return v_r_4988_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(
    mut v_00_u03b2_4989_: *mut crate::leanh::LeanObject,
    mut v_x_4990_: *mut crate::leanh::LeanObject,
    mut v_x_4991_: usize,
    mut v_x_4992_: usize,
    mut v_x_4993_: *mut crate::leanh::LeanObject,
    mut v_x_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___redArg(v_x_4990_, v_x_4991_, v_x_4992_, v_x_4993_, v_x_4994_);
    return v___x_4995_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7___boxed(
    mut v_00_u03b2_4996_: *mut crate::leanh::LeanObject,
    mut v_x_4997_: *mut crate::leanh::LeanObject,
    mut v_x_4998_: *mut crate::leanh::LeanObject,
    mut v_x_4999_: *mut crate::leanh::LeanObject,
    mut v_x_5000_: *mut crate::leanh::LeanObject,
    mut v_x_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1579__boxed_5002_: usize = 0;
    let mut v_x_1580__boxed_5003_: usize = 0;
    let mut v_res_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1579__boxed_5002_ = crate::leanh::lean_unbox_usize(v_x_4998_);
    crate::leanh::lean_dec(v_x_4998_);
    v_x_1580__boxed_5003_ = crate::leanh::lean_unbox_usize(v_x_4999_);
    crate::leanh::lean_dec(v_x_4999_);
    v_res_5004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7(v_00_u03b2_4996_, v_x_4997_, v_x_1579__boxed_5002_, v_x_1580__boxed_5003_, v_x_5000_, v_x_5001_);
    return v_res_5004_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(
    mut v_00_u03b2_5005_: *mut crate::leanh::LeanObject,
    mut v_keys_5006_: *mut crate::leanh::LeanObject,
    mut v_vals_5007_: *mut crate::leanh::LeanObject,
    mut v_heq_5008_: *mut crate::leanh::LeanObject,
    mut v_i_5009_: *mut crate::leanh::LeanObject,
    mut v_k_5010_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5011_: u8 = 0;
    v___x_5011_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___redArg(v_keys_5006_, v_i_5009_, v_k_5010_);
    return v___x_5011_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6___boxed(
    mut v_00_u03b2_5012_: *mut crate::leanh::LeanObject,
    mut v_keys_5013_: *mut crate::leanh::LeanObject,
    mut v_vals_5014_: *mut crate::leanh::LeanObject,
    mut v_heq_5015_: *mut crate::leanh::LeanObject,
    mut v_i_5016_: *mut crate::leanh::LeanObject,
    mut v_k_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5018_: u8 = 0;
    let mut v_r_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__6(v_00_u03b2_5012_, v_keys_5013_, v_vals_5014_, v_heq_5015_, v_i_5016_, v_k_5017_);
    crate::leanh::lean_dec_ref(v_k_5017_);
    crate::leanh::lean_dec_ref(v_vals_5014_);
    crate::leanh::lean_dec_ref(v_keys_5013_);
    v_r_5019_ = crate::leanh::lean_box((v_res_5018_) as usize);
    return v_r_5019_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9(
    mut v_00_u03b2_5020_: *mut crate::leanh::LeanObject,
    mut v_n_5021_: *mut crate::leanh::LeanObject,
    mut v_k_5022_: *mut crate::leanh::LeanObject,
    mut v_v_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9___redArg(v_n_5021_, v_k_5022_, v_v_5023_);
    return v___x_5024_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(
    mut v_00_u03b2_5025_: *mut crate::leanh::LeanObject,
    mut v_depth_5026_: usize,
    mut v_keys_5027_: *mut crate::leanh::LeanObject,
    mut v_vals_5028_: *mut crate::leanh::LeanObject,
    mut v_heq_5029_: *mut crate::leanh::LeanObject,
    mut v_i_5030_: *mut crate::leanh::LeanObject,
    mut v_entries_5031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___redArg(v_depth_5026_, v_keys_5027_, v_vals_5028_, v_i_5030_, v_entries_5031_);
    return v___x_5032_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10___boxed(
    mut v_00_u03b2_5033_: *mut crate::leanh::LeanObject,
    mut v_depth_5034_: *mut crate::leanh::LeanObject,
    mut v_keys_5035_: *mut crate::leanh::LeanObject,
    mut v_vals_5036_: *mut crate::leanh::LeanObject,
    mut v_heq_5037_: *mut crate::leanh::LeanObject,
    mut v_i_5038_: *mut crate::leanh::LeanObject,
    mut v_entries_5039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5040_: usize = 0;
    let mut v_res_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5040_ = crate::leanh::lean_unbox_usize(v_depth_5034_);
    crate::leanh::lean_dec(v_depth_5034_);
    v_res_5041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__10(v_00_u03b2_5033_, v_depth_boxed_5040_, v_keys_5035_, v_vals_5036_, v_heq_5037_, v_i_5038_, v_entries_5039_);
    crate::leanh::lean_dec_ref(v_vals_5036_);
    crate::leanh::lean_dec_ref(v_keys_5035_);
    return v_res_5041_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10(
    mut v_00_u03b2_5042_: *mut crate::leanh::LeanObject,
    mut v_x_5043_: *mut crate::leanh::LeanObject,
    mut v_x_5044_: *mut crate::leanh::LeanObject,
    mut v_x_5045_: *mut crate::leanh::LeanObject,
    mut v_x_5046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5047_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4_spec__7_spec__9_spec__10___redArg(v_x_5043_, v_x_5044_, v_x_5045_, v_x_5046_);
    return v___x_5047_;
}
pub unsafe fn l_Lean_Server_handleCodeActionResolve___lam__0(
    mut v_params_5049_: *mut crate::leanh::LeanObject,
    mut v_providerResultIndex_5050_: *mut crate::leanh::LeanObject,
    mut v_param_5051_: *mut crate::leanh::LeanObject,
    mut v_providerName_5052_: *mut crate::leanh::LeanObject,
    mut v_snap_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cap_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: u8 = 0;
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazy_x3f_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5082_: u8 = 0;
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v_a_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut v_a_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5117_: u8 = 0;
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5121_: u8 = 0;
    let mut v_val_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5108_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders;
                v___x_5109_ = lean_st_ref_get(v___x_5108_);
                v___x_5110_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5109_, v_providerName_5052_);
                crate::leanh::lean_dec(v___x_5109_);
                if crate::leanh::lean_obj_tag(v___x_5110_) == 0 {
                    v___x_5111_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_evalCodeActionProviderUnsafe___at___00Lean_Server_handleCodeAction_spec__2___boxed as *mut core::ffi::c_void, 5, 1);
                    crate::leanh::lean_closure_set(v___x_5111_, 0, v_providerName_5052_);
                    crate::leanh::lean_inc_ref(v_snap_5053_);
                    v___x_5112_ = l_Lean_Server_RequestM_runCoreM___redArg(
                        v_snap_5053_,
                        v___x_5111_,
                        v___y_5054_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5112_) == 0 {
                        v_a_5113_ = crate::leanh::lean_ctor_get(v___x_5112_, 0);
                        crate::leanh::lean_inc(v_a_5113_);
                        crate::leanh::lean_dec_ref_known(v___x_5112_, 1);
                        v_cap_5057_ = v_a_5113_;
                        v___y_5058_ = v___y_5054_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_snap_5053_);
                        crate::leanh::lean_dec_ref(v_param_5051_);
                        crate::leanh::lean_dec(v_providerResultIndex_5050_);
                        crate::leanh::lean_dec_ref(v_params_5049_);
                        v_a_5114_ = crate::leanh::lean_ctor_get(v___x_5112_, 0);
                        v_isSharedCheck_5121_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5112_)) as u8;
                        if v_isSharedCheck_5121_ == 0 {
                            v___x_5116_ = v___x_5112_;
                            v_isShared_5117_ = v_isSharedCheck_5121_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5114_);
                            crate::leanh::lean_dec(v___x_5112_);
                            v___x_5116_ = crate::leanh::lean_box(0);
                            v_isShared_5117_ = v_isSharedCheck_5121_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_providerName_5052_);
                    v_val_5122_ = crate::leanh::lean_ctor_get(v___x_5110_, 0);
                    crate::leanh::lean_inc(v_val_5122_);
                    crate::leanh::lean_dec_ref_known(v___x_5110_, 1);
                    v_cap_5057_ = v_val_5122_;
                    v___y_5058_ = v___y_5054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_5058_);
                v___x_5059_ = crate::leanh::lean_apply_4(
                    v_cap_5057_,
                    v_params_5049_,
                    v_snap_5053_,
                    v___y_5058_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5059_) == 0 {
                    v_a_5060_ = crate::leanh::lean_ctor_get(v___x_5059_, 0);
                    v_isSharedCheck_5099_ = (!crate::leanh::lean_is_exclusive(v___x_5059_)) as u8;
                    if v_isSharedCheck_5099_ == 0 {
                        v___x_5062_ = v___x_5059_;
                        v_isShared_5063_ = v_isSharedCheck_5099_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5060_);
                        crate::leanh::lean_dec(v___x_5059_);
                        v___x_5062_ = crate::leanh::lean_box(0);
                        v_isShared_5063_ = v_isSharedCheck_5099_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_param_5051_);
                    crate::leanh::lean_dec(v_providerResultIndex_5050_);
                    v_a_5100_ = crate::leanh::lean_ctor_get(v___x_5059_, 0);
                    v_isSharedCheck_5107_ = (!crate::leanh::lean_is_exclusive(v___x_5059_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5102_ = v___x_5059_;
                        v_isShared_5103_ = v_isSharedCheck_5107_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5100_);
                        crate::leanh::lean_dec(v___x_5059_);
                        v___x_5102_ = crate::leanh::lean_box(0);
                        v_isShared_5103_ = v_isSharedCheck_5107_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5064_ = lean_array_get_size(v_a_5060_);
                v___x_5065_ = lean_nat_dec_lt(v_providerResultIndex_5050_, v___x_5064_);
                if v___x_5065_ == 0 {
                    crate::leanh::lean_dec(v_a_5060_);
                    crate::leanh::lean_dec_ref(v_param_5051_);
                    v___x_5066_ = l_Lean_Server_handleCodeActionResolve___lam__0___closed__0;
                    v___x_5067_ = l_Nat_reprFast(v_providerResultIndex_5050_);
                    v___x_5068_ = lean_string_append(v___x_5066_, v___x_5067_);
                    crate::leanh::lean_dec_ref(v___x_5067_);
                    v___x_5069_ =
                        l_Lean_Server_instFromJsonCodeActionResolveData_fromJson___closed__5;
                    v___x_5070_ = lean_string_append(v___x_5068_, v___x_5069_);
                    v___x_5071_ = l_Lean_Server_RequestError_internalError(v___x_5070_);
                    if v_isShared_5063_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5062_, 1);
                        crate::leanh::lean_ctor_set(v___x_5062_, 0, v___x_5071_);
                        v___x_5073_ = v___x_5062_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5071_);
                        v___x_5073_ = v_reuseFailAlloc_5074_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5075_ = lean_array_fget(v_a_5060_, v_providerResultIndex_5050_);
                    crate::leanh::lean_dec(v_providerResultIndex_5050_);
                    crate::leanh::lean_dec(v_a_5060_);
                    v_lazy_x3f_5076_ = crate::leanh::lean_ctor_get(v___x_5075_, 1);
                    crate::leanh::lean_inc(v_lazy_x3f_5076_);
                    crate::leanh::lean_dec(v___x_5075_);
                    if crate::leanh::lean_obj_tag(v_lazy_x3f_5076_) == 1 {
                        crate::leanh::lean_del_object(v___x_5062_);
                        crate::leanh::lean_dec_ref(v_param_5051_);
                        v_val_5077_ = crate::leanh::lean_ctor_get(v_lazy_x3f_5076_, 0);
                        crate::leanh::lean_inc(v_val_5077_);
                        crate::leanh::lean_dec_ref_known(v_lazy_x3f_5076_, 1);
                        v___x_5078_ =
                            crate::leanh::lean_apply_1(v_val_5077_, crate::leanh::lean_box(0));
                        if crate::leanh::lean_obj_tag(v___x_5078_) == 0 {
                            v_a_5079_ = crate::leanh::lean_ctor_get(v___x_5078_, 0);
                            v_isSharedCheck_5086_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5078_)) as u8;
                            if v_isSharedCheck_5086_ == 0 {
                                v___x_5081_ = v___x_5078_;
                                v_isShared_5082_ = v_isSharedCheck_5086_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5079_);
                                crate::leanh::lean_dec(v___x_5078_);
                                v___x_5081_ = crate::leanh::lean_box(0);
                                v_isShared_5082_ = v_isSharedCheck_5086_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_5087_ = crate::leanh::lean_ctor_get(v___x_5078_, 0);
                            v_isSharedCheck_5095_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5078_)) as u8;
                            if v_isSharedCheck_5095_ == 0 {
                                v___x_5089_ = v___x_5078_;
                                v_isShared_5090_ = v_isSharedCheck_5095_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5087_);
                                crate::leanh::lean_dec(v___x_5078_);
                                v___x_5089_ = crate::leanh::lean_box(0);
                                v_isShared_5090_ = v_isSharedCheck_5095_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_lazy_x3f_5076_);
                        if v_isShared_5063_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5062_, 0, v_param_5051_);
                            v___x_5097_ = v___x_5062_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_5098_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_param_5051_);
                            v___x_5097_ = v_reuseFailAlloc_5098_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_5073_;
            }
            4 => {
                if v_isShared_5082_ == 0 {
                    v___x_5084_ = v___x_5081_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
                    v___x_5084_ = v_reuseFailAlloc_5085_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5084_;
            }
            6 => {
                v___x_5091_ = l_Lean_Server_RequestError_ofIoError(v_a_5087_);
                if v_isShared_5090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5089_, 0, v___x_5091_);
                    v___x_5093_ = v___x_5089_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5091_);
                    v___x_5093_ = v_reuseFailAlloc_5094_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5093_;
            }
            8 => {
                return v___x_5097_;
            }
            9 => {
                if v_isShared_5103_ == 0 {
                    v___x_5105_ = v___x_5102_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5105_;
            }
            11 => {
                if v_isShared_5117_ == 0 {
                    v___x_5119_ = v___x_5116_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
                    v___x_5119_ = v_reuseFailAlloc_5120_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleCodeActionResolve___lam__0___boxed(
    mut v_params_5123_: *mut crate::leanh::LeanObject,
    mut v_providerResultIndex_5124_: *mut crate::leanh::LeanObject,
    mut v_param_5125_: *mut crate::leanh::LeanObject,
    mut v_providerName_5126_: *mut crate::leanh::LeanObject,
    mut v_snap_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_Lean_Server_handleCodeActionResolve___lam__0(
        v_params_5123_,
        v_providerResultIndex_5124_,
        v_param_5125_,
        v_providerName_5126_,
        v_snap_5127_,
        v___y_5128_,
    );
    crate::leanh::lean_dec_ref(v___y_5128_);
    return v_res_5130_;
}
pub unsafe fn l_Lean_Server_handleCodeActionResolve___lam__2(
    mut v___x_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5134_, 0, v___x_5131_);
    return v___x_5134_;
}
pub unsafe fn l_Lean_Server_handleCodeActionResolve___lam__2___boxed(
    mut v___x_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Lean_Server_handleCodeActionResolve___lam__2(v___x_5135_, v___y_5136_);
    crate::leanh::lean_dec_ref(v___y_5136_);
    return v_res_5138_;
}
pub unsafe fn l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(
    mut v_params_5139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5144_: u8 = 0;
    let mut v___x_5145_: u8 = 0;
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v_a_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_params_5139_);
                v___x_5140_ =
                    l_Lean_Server_instFromJsonCodeActionResolveData_fromJson(v_params_5139_);
                if crate::leanh::lean_obj_tag(v___x_5140_) == 0 {
                    v_a_5141_ = crate::leanh::lean_ctor_get(v___x_5140_, 0);
                    v_isSharedCheck_5156_ = (!crate::leanh::lean_is_exclusive(v___x_5140_)) as u8;
                    if v_isSharedCheck_5156_ == 0 {
                        v___x_5143_ = v___x_5140_;
                        v_isShared_5144_ = v_isSharedCheck_5156_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5141_);
                        crate::leanh::lean_dec(v___x_5140_);
                        v___x_5143_ = crate::leanh::lean_box(0);
                        v_isShared_5144_ = v_isSharedCheck_5156_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_params_5139_);
                    v_a_5157_ = crate::leanh::lean_ctor_get(v___x_5140_, 0);
                    v_isSharedCheck_5164_ = (!crate::leanh::lean_is_exclusive(v___x_5140_)) as u8;
                    if v_isSharedCheck_5164_ == 0 {
                        v___x_5159_ = v___x_5140_;
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5157_);
                        crate::leanh::lean_dec(v___x_5140_);
                        v___x_5159_ = crate::leanh::lean_box(0);
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5145_ = 3;
                v___x_5146_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0;
                v___x_5147_ = l_Lean_Json_compress(v_params_5139_);
                v___x_5148_ = lean_string_append(v___x_5146_, v___x_5147_);
                crate::leanh::lean_dec_ref(v___x_5147_);
                v___x_5149_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1;
                v___x_5150_ = lean_string_append(v___x_5148_, v___x_5149_);
                v___x_5151_ = lean_string_append(v___x_5150_, v_a_5141_);
                crate::leanh::lean_dec(v_a_5141_);
                v___x_5152_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5152_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5145_,
                );
                if v_isShared_5144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5143_, 0, v___x_5152_);
                    v___x_5154_ = v___x_5143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5154_;
            }
            3 => {
                if v_isShared_5160_ == 0 {
                    v___x_5162_ = v___x_5159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
                    v___x_5162_ = v_reuseFailAlloc_5163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(
    mut v_params_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5171_: u8 = 0;
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5175_: u8 = 0;
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5167_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0_spec__0(v_params_5165_);
                if crate::leanh::lean_obj_tag(v___x_5167_) == 0 {
                    v_a_5168_ = crate::leanh::lean_ctor_get(v___x_5167_, 0);
                    v_isSharedCheck_5175_ = (!crate::leanh::lean_is_exclusive(v___x_5167_)) as u8;
                    if v_isSharedCheck_5175_ == 0 {
                        v___x_5170_ = v___x_5167_;
                        v_isShared_5171_ = v_isSharedCheck_5175_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5168_);
                        crate::leanh::lean_dec(v___x_5167_);
                        v___x_5170_ = crate::leanh::lean_box(0);
                        v_isShared_5171_ = v_isSharedCheck_5175_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5176_ = crate::leanh::lean_ctor_get(v___x_5167_, 0);
                    v_isSharedCheck_5183_ = (!crate::leanh::lean_is_exclusive(v___x_5167_)) as u8;
                    if v_isSharedCheck_5183_ == 0 {
                        v___x_5178_ = v___x_5167_;
                        v_isShared_5179_ = v_isSharedCheck_5183_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5176_);
                        crate::leanh::lean_dec(v___x_5167_);
                        v___x_5178_ = crate::leanh::lean_box(0);
                        v_isShared_5179_ = v_isSharedCheck_5183_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5171_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5170_, 1);
                    v___x_5173_ = v___x_5170_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
                    v___x_5173_ = v_reuseFailAlloc_5174_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5173_;
            }
            3 => {
                if v_isShared_5179_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5178_, 0);
                    v___x_5181_ = v___x_5178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5182_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg___boxed(
    mut v_params_5184_: *mut crate::leanh::LeanObject,
    mut v_a_5185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5186_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_params_5184_);
    return v_res_5186_;
}
pub unsafe fn _init_l_Lean_Server_handleCodeActionResolve___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = l_Lean_Server_handleCodeActionResolve___closed__0;
    v___x_5189_ = l_Lean_Server_RequestError_internalError(v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn _init_l_Lean_Server_handleCodeActionResolve___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5190_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_handleCodeActionResolve___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Server_handleCodeActionResolve___closed__1_once),
        _init_l_Lean_Server_handleCodeActionResolve___closed__1,
    );
    v___f_5191_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_handleCodeActionResolve___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5191_, 0, v___x_5190_);
    return v___f_5191_;
}
pub unsafe fn _init_l_Lean_Server_handleCodeActionResolve___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5193_ = l_Lean_Server_handleCodeActionResolve___closed__3;
    v___x_5194_ = l_Lean_Server_RequestError_invalidParams(v___x_5193_);
    return v___x_5194_;
}
pub unsafe fn l_Lean_Server_handleCodeActionResolve(
    mut v_param_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_providerName_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_providerResultIndex_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5224_: u8 = 0;
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5232_: u8 = 0;
    let mut v_unused_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5198_ =
                    l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleCodeAction_spec__6(
                        v_a_5196_,
                    );
                v_data_x3f_5199_ = crate::leanh::lean_ctor_get(v_param_5195_, 9);
                if crate::leanh::lean_obj_tag(v_data_x3f_5199_) == 1 {
                    v_a_5200_ = crate::leanh::lean_ctor_get(v___x_5198_, 0);
                    crate::leanh::lean_inc(v_a_5200_);
                    crate::leanh::lean_dec_ref(v___x_5198_);
                    v_val_5201_ = crate::leanh::lean_ctor_get(v_data_x3f_5199_, 0);
                    crate::leanh::lean_inc(v_val_5201_);
                    v___x_5202_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_val_5201_);
                    if crate::leanh::lean_obj_tag(v___x_5202_) == 0 {
                        v_toEditableDocumentCore_5203_ = crate::leanh::lean_ctor_get(v_a_5200_, 0);
                        v_meta_5204_ =
                            crate::leanh::lean_ctor_get(v_toEditableDocumentCore_5203_, 0);
                        v_a_5205_ = crate::leanh::lean_ctor_get(v___x_5202_, 0);
                        crate::leanh::lean_inc(v_a_5205_);
                        crate::leanh::lean_dec_ref_known(v___x_5202_, 1);
                        v_params_5206_ = crate::leanh::lean_ctor_get(v_a_5205_, 0);
                        crate::leanh::lean_inc_ref(v_params_5206_);
                        v_range_5207_ = crate::leanh::lean_ctor_get(v_params_5206_, 3);
                        v_text_5208_ = crate::leanh::lean_ctor_get(v_meta_5204_, 3);
                        v_providerName_5209_ = crate::leanh::lean_ctor_get(v_a_5205_, 1);
                        crate::leanh::lean_inc(v_providerName_5209_);
                        v_providerResultIndex_5210_ = crate::leanh::lean_ctor_get(v_a_5205_, 2);
                        crate::leanh::lean_inc(v_providerResultIndex_5210_);
                        crate::leanh::lean_dec(v_a_5205_);
                        v_end_5211_ = crate::leanh::lean_ctor_get(v_range_5207_, 1);
                        crate::leanh::lean_inc_ref(v_end_5211_);
                        v___f_5212_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Server_handleCodeActionResolve___lam__0___boxed
                                as *mut core::ffi::c_void,
                            7,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_5212_, 0, v_params_5206_);
                        crate::leanh::lean_closure_set(v___f_5212_, 1, v_providerResultIndex_5210_);
                        crate::leanh::lean_closure_set(v___f_5212_, 2, v_param_5195_);
                        crate::leanh::lean_closure_set(v___f_5212_, 3, v_providerName_5209_);
                        v___x_5213_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_5208_, v_end_5211_);
                        v___f_5214_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Server_handleCodeAction___lam__2___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_5214_, 0, v___x_5213_);
                        v___f_5215_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_handleCodeActionResolve___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_handleCodeActionResolve___closed__2_once
                            ),
                            _init_l_Lean_Server_handleCodeActionResolve___closed__2,
                        );
                        v___x_5216_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(
                            v_a_5200_,
                            v___f_5214_,
                            v___f_5215_,
                            v___f_5212_,
                            v_a_5196_,
                        );
                        return v___x_5216_;
                    } else {
                        crate::leanh::lean_dec(v_a_5200_);
                        crate::leanh::lean_dec_ref(v_param_5195_);
                        v_a_5217_ = crate::leanh::lean_ctor_get(v___x_5202_, 0);
                        v_isSharedCheck_5224_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5202_)) as u8;
                        if v_isSharedCheck_5224_ == 0 {
                            v___x_5219_ = v___x_5202_;
                            v_isShared_5220_ = v_isSharedCheck_5224_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5217_);
                            crate::leanh::lean_dec(v___x_5202_);
                            v___x_5219_ = crate::leanh::lean_box(0);
                            v_isShared_5220_ = v_isSharedCheck_5224_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_param_5195_);
                    v_isSharedCheck_5232_ = (!crate::leanh::lean_is_exclusive(v___x_5198_)) as u8;
                    if v_isSharedCheck_5232_ == 0 {
                        v_unused_5233_ = crate::leanh::lean_ctor_get(v___x_5198_, 0);
                        crate::leanh::lean_dec(v_unused_5233_);
                        v___x_5226_ = v___x_5198_;
                        v_isShared_5227_ = v_isSharedCheck_5232_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5198_);
                        v___x_5226_ = crate::leanh::lean_box(0);
                        v_isShared_5227_ = v_isSharedCheck_5232_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5220_ == 0 {
                    v___x_5222_ = v___x_5219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
                    v___x_5222_ = v_reuseFailAlloc_5223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5222_;
            }
            3 => {
                v___x_5228_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_handleCodeActionResolve___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Server_handleCodeActionResolve___closed__4_once),
                    _init_l_Lean_Server_handleCodeActionResolve___closed__4,
                );
                if v_isShared_5227_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5226_, 1);
                    crate::leanh::lean_ctor_set(v___x_5226_, 0, v___x_5228_);
                    v___x_5230_ = v___x_5226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5228_);
                    v___x_5230_ = v_reuseFailAlloc_5231_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleCodeActionResolve___boxed(
    mut v_param_5234_: *mut crate::leanh::LeanObject,
    mut v_a_5235_: *mut crate::leanh::LeanObject,
    mut v_a_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_Server_handleCodeActionResolve(v_param_5234_, v_a_5235_);
    crate::leanh::lean_dec_ref(v_a_5235_);
    return v_res_5237_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(
    mut v_params_5238_: *mut crate::leanh::LeanObject,
    mut v_a_5239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5241_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___redArg(v_params_5238_);
    return v___x_5241_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0___boxed(
    mut v_params_5242_: *mut crate::leanh::LeanObject,
    mut v_a_5243_: *mut crate::leanh::LeanObject,
    mut v_a_5244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5245_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_handleCodeActionResolve_spec__0(v_params_5242_, v_a_5243_);
    crate::leanh::lean_dec_ref(v_a_5243_);
    return v_res_5245_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(
    mut v_serialize_x3f_5246_: *mut crate::leanh::LeanObject,
    mut v_a_5247_: u8,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5252_: u8 = 0;
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5256_: u8 = 0;
    let mut v_a_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5260_: u8 = 0;
    let mut v_val_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v_a_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5272_: u8 = 0;
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_5248_) == 0 {
                    crate::leanh::lean_dec(v_serialize_x3f_5246_);
                    v_a_5249_ = crate::leanh::lean_ctor_get(v___y_5248_, 0);
                    v_isSharedCheck_5256_ = (!crate::leanh::lean_is_exclusive(v___y_5248_)) as u8;
                    if v_isSharedCheck_5256_ == 0 {
                        v___x_5251_ = v___y_5248_;
                        v_isShared_5252_ = v_isSharedCheck_5256_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5249_);
                        crate::leanh::lean_dec(v___y_5248_);
                        v___x_5251_ = crate::leanh::lean_box(0);
                        v_isShared_5252_ = v_isSharedCheck_5256_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_serialize_x3f_5246_) == 1 {
                        v_a_5257_ = crate::leanh::lean_ctor_get(v___y_5248_, 0);
                        v_isSharedCheck_5268_ =
                            (!crate::leanh::lean_is_exclusive(v___y_5248_)) as u8;
                        if v_isSharedCheck_5268_ == 0 {
                            v___x_5259_ = v___y_5248_;
                            v_isShared_5260_ = v_isSharedCheck_5268_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5257_);
                            crate::leanh::lean_dec(v___y_5248_);
                            v___x_5259_ = crate::leanh::lean_box(0);
                            v_isShared_5260_ = v_isSharedCheck_5268_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_serialize_x3f_5246_);
                        v_a_5269_ = crate::leanh::lean_ctor_get(v___y_5248_, 0);
                        v_isSharedCheck_5280_ =
                            (!crate::leanh::lean_is_exclusive(v___y_5248_)) as u8;
                        if v_isSharedCheck_5280_ == 0 {
                            v___x_5271_ = v___y_5248_;
                            v_isShared_5272_ = v_isSharedCheck_5280_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5269_);
                            crate::leanh::lean_dec(v___y_5248_);
                            v___x_5271_ = crate::leanh::lean_box(0);
                            v_isShared_5272_ = v_isSharedCheck_5280_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5252_ == 0 {
                    v___x_5254_ = v___x_5251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
                    v___x_5254_ = v_reuseFailAlloc_5255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5254_;
            }
            3 => {
                v_val_5261_ = crate::leanh::lean_ctor_get(v_serialize_x3f_5246_, 0);
                crate::leanh::lean_inc(v_val_5261_);
                crate::leanh::lean_dec_ref_known(v_serialize_x3f_5246_, 1);
                v___x_5262_ = crate::leanh::lean_box(0);
                v___x_5263_ = crate::leanh::lean_apply_1(v_val_5261_, v_a_5257_);
                v___x_5264_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5264_, 0, v___x_5262_);
                crate::leanh::lean_ctor_set(v___x_5264_, 1, v___x_5263_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5264_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_a_5247_,
                );
                if v_isShared_5260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5259_, 0, v___x_5264_);
                    v___x_5266_ = v___x_5259_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5264_);
                    v___x_5266_ = v_reuseFailAlloc_5267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5266_;
            }
            5 => {
                v___x_5273_ = l_Lean_Lsp_instToJsonCodeAction_toJson(v_a_5269_);
                crate::leanh::lean_inc(v___x_5273_);
                v___x_5274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5274_, 0, v___x_5273_);
                v___x_5275_ = l_Lean_Json_compress(v___x_5273_);
                v___x_5276_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5276_, 0, v___x_5274_);
                crate::leanh::lean_ctor_set(v___x_5276_, 1, v___x_5275_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5276_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_a_5247_,
                );
                if v_isShared_5272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5271_, 0, v___x_5276_);
                    v___x_5278_ = v___x_5271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5276_);
                    v___x_5278_ = v_reuseFailAlloc_5279_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v_serialize_x3f_5281_: *mut crate::leanh::LeanObject,
    mut v_a_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_272__boxed_5284_: u8 = 0;
    let mut v_res_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_272__boxed_5284_ = (crate::leanh::lean_unbox(v_a_5282_) as u8);
    v_res_5285_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_5281_, v_a_272__boxed_5284_, v___y_5283_);
    return v_res_5285_;
}
pub unsafe fn l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(
    mut v_params_5286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v___x_5292_: u8 = 0;
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5303_: u8 = 0;
    let mut v_a_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5307_: u8 = 0;
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_params_5286_);
                v___x_5287_ = l_Lean_Lsp_instFromJsonCodeAction_fromJson(v_params_5286_);
                if crate::leanh::lean_obj_tag(v___x_5287_) == 0 {
                    v_a_5288_ = crate::leanh::lean_ctor_get(v___x_5287_, 0);
                    v_isSharedCheck_5303_ = (!crate::leanh::lean_is_exclusive(v___x_5287_)) as u8;
                    if v_isSharedCheck_5303_ == 0 {
                        v___x_5290_ = v___x_5287_;
                        v_isShared_5291_ = v_isSharedCheck_5303_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5288_);
                        crate::leanh::lean_dec(v___x_5287_);
                        v___x_5290_ = crate::leanh::lean_box(0);
                        v_isShared_5291_ = v_isSharedCheck_5303_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_params_5286_);
                    v_a_5304_ = crate::leanh::lean_ctor_get(v___x_5287_, 0);
                    v_isSharedCheck_5311_ = (!crate::leanh::lean_is_exclusive(v___x_5287_)) as u8;
                    if v_isSharedCheck_5311_ == 0 {
                        v___x_5306_ = v___x_5287_;
                        v_isShared_5307_ = v_isSharedCheck_5311_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5304_);
                        crate::leanh::lean_dec(v___x_5287_);
                        v___x_5306_ = crate::leanh::lean_box(0);
                        v_isShared_5307_ = v_isSharedCheck_5311_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5292_ = 3;
                v___x_5293_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__0;
                v___x_5294_ = l_Lean_Json_compress(v_params_5286_);
                v___x_5295_ = lean_string_append(v___x_5293_, v___x_5294_);
                crate::leanh::lean_dec_ref(v___x_5294_);
                v___x_5296_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__0___closed__1;
                v___x_5297_ = lean_string_append(v___x_5295_, v___x_5296_);
                v___x_5298_ = lean_string_append(v___x_5297_, v_a_5288_);
                crate::leanh::lean_dec(v_a_5288_);
                v___x_5299_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5299_, 0, v___x_5298_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5299_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5292_,
                );
                if v_isShared_5291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5290_, 0, v___x_5299_);
                    v___x_5301_ = v___x_5290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5299_);
                    v___x_5301_ = v_reuseFailAlloc_5302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5301_;
            }
            3 => {
                if v_isShared_5307_ == 0 {
                    v___x_5309_ = v___x_5306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
                    v___x_5309_ = v_reuseFailAlloc_5310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_params_5312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5322_: u8 = 0;
    let mut v_a_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5314_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(v_params_5312_);
                if crate::leanh::lean_obj_tag(v___x_5314_) == 0 {
                    v_a_5315_ = crate::leanh::lean_ctor_get(v___x_5314_, 0);
                    v_isSharedCheck_5322_ = (!crate::leanh::lean_is_exclusive(v___x_5314_)) as u8;
                    if v_isSharedCheck_5322_ == 0 {
                        v___x_5317_ = v___x_5314_;
                        v_isShared_5318_ = v_isSharedCheck_5322_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5315_);
                        crate::leanh::lean_dec(v___x_5314_);
                        v___x_5317_ = crate::leanh::lean_box(0);
                        v_isShared_5318_ = v_isSharedCheck_5322_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5323_ = crate::leanh::lean_ctor_get(v___x_5314_, 0);
                    v_isSharedCheck_5330_ = (!crate::leanh::lean_is_exclusive(v___x_5314_)) as u8;
                    if v_isSharedCheck_5330_ == 0 {
                        v___x_5325_ = v___x_5314_;
                        v_isShared_5326_ = v_isSharedCheck_5330_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5323_);
                        crate::leanh::lean_dec(v___x_5314_);
                        v___x_5325_ = crate::leanh::lean_box(0);
                        v_isShared_5326_ = v_isSharedCheck_5330_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5318_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5317_, 1);
                    v___x_5320_ = v___x_5317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
                    v___x_5320_ = v_reuseFailAlloc_5321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5320_;
            }
            3 => {
                if v_isShared_5326_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5325_, 0);
                    v___x_5328_ = v___x_5325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
                    v___x_5328_ = v_reuseFailAlloc_5329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_params_5331_: *mut crate::leanh::LeanObject,
    mut v_a_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5333_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5331_);
    return v_res_5333_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(
    mut v_handler_5334_: *mut crate::leanh::LeanObject,
    mut v___f_5335_: *mut crate::leanh::LeanObject,
    mut v_j_5336_: *mut crate::leanh::LeanObject,
    mut v___y_5337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5345_: u8 = 0;
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut v_a_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_a_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5362_: u8 = 0;
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5339_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_5336_);
                if crate::leanh::lean_obj_tag(v___x_5339_) == 0 {
                    v_a_5340_ = crate::leanh::lean_ctor_get(v___x_5339_, 0);
                    crate::leanh::lean_inc(v_a_5340_);
                    crate::leanh::lean_dec_ref_known(v___x_5339_, 1);
                    crate::leanh::lean_inc_ref(v___y_5337_);
                    v___x_5341_ = crate::leanh::lean_apply_3(
                        v_handler_5334_,
                        v_a_5340_,
                        v___y_5337_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5341_) == 0 {
                        v_a_5342_ = crate::leanh::lean_ctor_get(v___x_5341_, 0);
                        v_isSharedCheck_5350_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5341_)) as u8;
                        if v_isSharedCheck_5350_ == 0 {
                            v___x_5344_ = v___x_5341_;
                            v_isShared_5345_ = v_isSharedCheck_5350_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5342_);
                            crate::leanh::lean_dec(v___x_5341_);
                            v___x_5344_ = crate::leanh::lean_box(0);
                            v_isShared_5345_ = v_isSharedCheck_5350_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_5335_);
                        v_a_5351_ = crate::leanh::lean_ctor_get(v___x_5341_, 0);
                        v_isSharedCheck_5358_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5341_)) as u8;
                        if v_isSharedCheck_5358_ == 0 {
                            v___x_5353_ = v___x_5341_;
                            v_isShared_5354_ = v_isSharedCheck_5358_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5351_);
                            crate::leanh::lean_dec(v___x_5341_);
                            v___x_5353_ = crate::leanh::lean_box(0);
                            v_isShared_5354_ = v_isSharedCheck_5358_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_5335_);
                    crate::leanh::lean_dec_ref(v_handler_5334_);
                    v_a_5359_ = crate::leanh::lean_ctor_get(v___x_5339_, 0);
                    v_isSharedCheck_5366_ = (!crate::leanh::lean_is_exclusive(v___x_5339_)) as u8;
                    if v_isSharedCheck_5366_ == 0 {
                        v___x_5361_ = v___x_5339_;
                        v_isShared_5362_ = v_isSharedCheck_5366_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5359_);
                        crate::leanh::lean_dec(v___x_5339_);
                        v___x_5361_ = crate::leanh::lean_box(0);
                        v_isShared_5362_ = v_isSharedCheck_5366_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5346_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5335_, v_a_5342_);
                if v_isShared_5345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5344_, 0, v___x_5346_);
                    v___x_5348_ = v___x_5344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5346_);
                    v___x_5348_ = v_reuseFailAlloc_5349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5348_;
            }
            3 => {
                if v_isShared_5354_ == 0 {
                    v___x_5356_ = v___x_5353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
                    v___x_5356_ = v_reuseFailAlloc_5357_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5356_;
            }
            5 => {
                if v_isShared_5362_ == 0 {
                    v___x_5364_ = v___x_5361_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5359_);
                    v___x_5364_ = v_reuseFailAlloc_5365_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed(
    mut v_handler_5367_: *mut crate::leanh::LeanObject,
    mut v___f_5368_: *mut crate::leanh::LeanObject,
    mut v_j_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5372_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2(v_handler_5367_, v___f_5368_, v_j_5369_, v___y_5370_);
    crate::leanh::lean_dec_ref(v___y_5370_);
    return v_res_5372_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__0(
    mut v_j_5373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5378_: u8 = 0;
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5382_: u8 = 0;
    let mut v_a_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5386_: u8 = 0;
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5374_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__0(v_j_5373_);
                if crate::leanh::lean_obj_tag(v___x_5374_) == 0 {
                    v_a_5375_ = crate::leanh::lean_ctor_get(v___x_5374_, 0);
                    v_isSharedCheck_5382_ = (!crate::leanh::lean_is_exclusive(v___x_5374_)) as u8;
                    if v_isSharedCheck_5382_ == 0 {
                        v___x_5377_ = v___x_5374_;
                        v_isShared_5378_ = v_isSharedCheck_5382_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5375_);
                        crate::leanh::lean_dec(v___x_5374_);
                        v___x_5377_ = crate::leanh::lean_box(0);
                        v_isShared_5378_ = v_isSharedCheck_5382_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5383_ = crate::leanh::lean_ctor_get(v___x_5374_, 0);
                    v_isSharedCheck_5391_ = (!crate::leanh::lean_is_exclusive(v___x_5374_)) as u8;
                    if v_isSharedCheck_5391_ == 0 {
                        v___x_5385_ = v___x_5374_;
                        v_isShared_5386_ = v_isSharedCheck_5391_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5383_);
                        crate::leanh::lean_dec(v___x_5374_);
                        v___x_5385_ = crate::leanh::lean_box(0);
                        v_isShared_5386_ = v_isSharedCheck_5391_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5378_ == 0 {
                    v___x_5380_ = v___x_5377_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
                    v___x_5380_ = v_reuseFailAlloc_5381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5380_;
            }
            3 => {
                v___x_5387_ = l_Lean_Server_CodeAction_getFileSource_x21(v_a_5383_);
                if v_isShared_5386_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5385_, 0, v___x_5387_);
                    v___x_5389_ = v___x_5385_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5387_);
                    v___x_5389_ = v_reuseFailAlloc_5390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(
    mut v_method_5393_: *mut crate::leanh::LeanObject,
    mut v_handler_5394_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_5395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5401_: u8 = 0;
    let mut v___x_5402_: u8 = 0;
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: u8 = 0;
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5432_: u8 = 0;
    let mut v_a_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5397_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_5397_) == 0 {
                    v_a_5398_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                    v_isSharedCheck_5432_ = (!crate::leanh::lean_is_exclusive(v___x_5397_)) as u8;
                    if v_isSharedCheck_5432_ == 0 {
                        v___x_5400_ = v___x_5397_;
                        v_isShared_5401_ = v_isSharedCheck_5432_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5398_);
                        crate::leanh::lean_dec(v___x_5397_);
                        v___x_5400_ = crate::leanh::lean_box(0);
                        v_isShared_5401_ = v_isSharedCheck_5432_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_serialize_x3f_5395_);
                    crate::leanh::lean_dec_ref(v_handler_5394_);
                    crate::leanh::lean_dec_ref(v_method_5393_);
                    v_a_5433_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                    v_isSharedCheck_5440_ = (!crate::leanh::lean_is_exclusive(v___x_5397_)) as u8;
                    if v_isSharedCheck_5440_ == 0 {
                        v___x_5435_ = v___x_5397_;
                        v_isShared_5436_ = v_isSharedCheck_5440_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5433_);
                        crate::leanh::lean_dec(v___x_5397_);
                        v___x_5435_ = crate::leanh::lean_box(0);
                        v_isShared_5436_ = v_isSharedCheck_5440_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5402_ = (crate::leanh::lean_unbox(v_a_5398_) as u8);
                if v___x_5402_ == 0 {
                    crate::leanh::lean_dec(v_a_5398_);
                    crate::leanh::lean_dec(v_serialize_x3f_5395_);
                    crate::leanh::lean_dec_ref(v_handler_5394_);
                    v___x_5403_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0;
                    v___x_5404_ = lean_string_append(v___x_5403_, v_method_5393_);
                    crate::leanh::lean_dec_ref(v_method_5393_);
                    v___x_5405_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__1;
                    v___x_5406_ = lean_string_append(v___x_5404_, v___x_5405_);
                    v___x_5407_ = lean_mk_io_user_error(v___x_5406_);
                    if v_isShared_5401_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5400_, 1);
                        crate::leanh::lean_ctor_set(v___x_5400_, 0, v___x_5407_);
                        v___x_5409_ = v___x_5400_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
                        v___x_5409_ = v_reuseFailAlloc_5410_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5411_ = l_Lean_Server_requestHandlers;
                    v___x_5412_ = lean_st_ref_get(v___x_5411_);
                    v___x_5413_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5412_, v_method_5393_);
                    crate::leanh::lean_dec(v___x_5412_);
                    if v___x_5413_ == 0 {
                        v___x_5414_ = lean_st_ref_take(v___x_5411_);
                        v___f_5415_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___closed__0;
                        v___f_5416_ = crate::leanh::lean_alloc_closure(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_5416_, 0, v_serialize_x3f_5395_);
                        crate::leanh::lean_closure_set(v___f_5416_, 1, v_a_5398_);
                        v___f_5417_ = crate::leanh::lean_alloc_closure(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___lam__2___boxed as *mut core::ffi::c_void, 5, 2);
                        crate::leanh::lean_closure_set(v___f_5417_, 0, v_handler_5394_);
                        crate::leanh::lean_closure_set(v___f_5417_, 1, v___f_5416_);
                        v___x_5418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5418_, 0, v___f_5415_);
                        crate::leanh::lean_ctor_set(v___x_5418_, 1, v___f_5417_);
                        v___x_5419_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0_spec__4___redArg(v___x_5414_, v_method_5393_, v___x_5418_);
                        v___x_5420_ = lean_st_ref_set(v___x_5411_, v___x_5419_);
                        if v_isShared_5401_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5400_, 0, v___x_5420_);
                            v___x_5422_ = v___x_5400_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5423_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
                            v___x_5422_ = v_reuseFailAlloc_5423_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5398_);
                        crate::leanh::lean_dec(v_serialize_x3f_5395_);
                        crate::leanh::lean_dec_ref(v_handler_5394_);
                        v___x_5424_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__0;
                        v___x_5425_ = lean_string_append(v___x_5424_, v_method_5393_);
                        crate::leanh::lean_dec_ref(v_method_5393_);
                        v___x_5426_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2__spec__0___closed__3;
                        v___x_5427_ = lean_string_append(v___x_5425_, v___x_5426_);
                        v___x_5428_ = lean_mk_io_user_error(v___x_5427_);
                        if v_isShared_5401_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5400_, 1);
                            crate::leanh::lean_ctor_set(v___x_5400_, 0, v___x_5428_);
                            v___x_5430_ = v___x_5400_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5431_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5428_);
                            v___x_5430_ = v_reuseFailAlloc_5431_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5409_;
            }
            3 => {
                return v___x_5422_;
            }
            4 => {
                return v___x_5430_;
            }
            5 => {
                if v_isShared_5436_ == 0 {
                    v___x_5438_ = v___x_5435_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
                    v___x_5438_ = v_reuseFailAlloc_5439_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0___boxed(
    mut v_method_5441_: *mut crate::leanh::LeanObject,
    mut v_handler_5442_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_5443_: *mut crate::leanh::LeanObject,
    mut v_a_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5445_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(v_method_5441_, v_handler_5442_, v_serialize_x3f_5443_);
    return v_res_5445_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5449_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_;
    v___x_5450_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_;
    v___x_5451_ = crate::leanh::lean_box(0);
    v___x_5452_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0(v___x_5449_, v___x_5450_, v___x_5451_);
    return v___x_5452_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2____boxed(
    mut v_a_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_();
    return v_res_5454_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(
    mut v_params_5455_: *mut crate::leanh::LeanObject,
    mut v_a_5456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5458_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5455_);
    return v___x_5458_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_params_5459_: *mut crate::leanh::LeanObject,
    mut v_a_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5462_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2__spec__0_spec__1(v_params_5459_, v_a_5460_);
    crate::leanh::lean_dec_ref(v_a_5460_);
    return v_res_5462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Requests(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_2573400817____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_builtinCodeActionProviders,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_454587247____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_codeActionProviderExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_codeActionProviderExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1656927832____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_275661449____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_CodeActions_Basic_1161087171____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_Basic(
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
pub unsafe fn initialize_Lean_Server_CodeActions_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Requests(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_Basic(builtin);
}
